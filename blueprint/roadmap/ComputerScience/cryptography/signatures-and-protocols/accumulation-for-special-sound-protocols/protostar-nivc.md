# ProtoStar: non-uniform IVC with one accumulator and a one-hot circuit selector

Let $C_1,\dots,C_I$ be branch circuits of a Plonkish relation with high-degree gates and lookups, with a program counter $\mathrm{pc}$ selecting the circuit executed at each step. Encode the selection by a vector $b\in\mathbb{F}^{I}$ checked with the degree-two equations $b_i(\mathrm{pc}-i)=0$ and $b_i(b_i-1)=0$ for all $i$ and $\sum_ib_i=1$, which force $b$ to be the indicator of $\mathrm{pc}$, and gate each branch's constraints by $b_i$. The prover's witness for all branches is then sparse: only the executed circuit's witness is nonzero. Compiling the resulting special-sound protocol with ProtoStar's generic accumulation gives, under the Fiat–Shamir heuristic and with a binding homomorphic commitment, an IVC scheme with a single running accumulator in which, for one degree-$d$ gate type, the recursive circuit performs $3$ group scalar multiplications, $d+4$ field operations and $d+O(1)$ hash operations, independently of $I$. The per-step prover depends on the executed circuit: committing to the sparse witness costs group operations proportional to its nonzero entries plus the lookups, and the error terms are computed in time $O(d\,|C_{\mathrm{pc}}|)$ rather than $O(d(|C_1|+\dots+|C_I|))$; overall the prover's dependence on the number of supported circuits is at most logarithmic. Separately, the lookup argument makes the prover's work independent of the table size, assuming free indexing in the table. The final decider still evaluates all branch circuits, with $O(n+\sum_iC_i+T+\ell_{\mathrm{lk}})$ field operations for $n$ gates, a table of size $T$ and $\ell_{\mathrm{lk}}$ lookups.

## Proof sketch

The selector protocol is a one-move special-sound protocol with a degree-two verifier, so it composes with the high-degree gate and lookup protocols into one special-sound protocol for the multi-circuit relation, to which the generic compiler applies. Because only the executed branch's witness is nonzero, folding the witness into the accumulator costs work proportional to that branch, and splitting the gated checks into $I$ branch gates, of which one is active, lets the error terms be computed with caching from the active branch alone.

## Depends on

- [Non-uniform incrementally verifiable computation](../customizable-constraint-systems-and-multi-folding/non-uniform-ivc.md)
- [Split accumulation and NARKs with accumulation](../incrementally-verifiable-computation-and-pcd/split-accumulation.md)

## Proof depends on

- [ProtoStar: generic accumulation for special-sound protocols](protostar-accumulation.md)
- [Logarithmic-derivative lookups as a degree-two special-sound protocol](protostar-lookup-special-sound.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620, abstract, Section 1, Section 4.5 (circuit selection), Section 6 and Corollary 1.
