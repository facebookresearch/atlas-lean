# Preserving equivalences does not preserve robust safety

For a [compilation chain](compilation-chains-and-robust-satisfaction.md) whose compiler also maps source contexts $\mathsf C_S$ to $\mathsf C_S{\downarrow}$ and whole programs $W$ to
$W{\downarrow}$, consider the correctness criteria
$\mathrm{TP}$: $\forall W, t.\ W{\downarrow} \rightsquigarrow t \Rightarrow W \rightsquigarrow t$ for whole programs $W$ (backward simulation);
$\mathrm{SCC}$: $\forall \mathsf P, \mathsf C_S, t.\ \mathsf C_S{\downarrow}[\mathsf P{\downarrow}] \rightsquigarrow t \Rightarrow \mathsf C_S[\mathsf P] \rightsquigarrow t$ (separate compiler correctness, linking with
compiled source contexts); and $\mathrm{CCC}$: $\mathbf C_T \approx \mathsf C_S$, $\mathsf C_S$ linkable with $\mathsf P$, and $\mathbf C_T[\mathsf P{\downarrow}] \rightsquigarrow t$ imply $\mathsf C_S[\mathsf P] \rightsquigarrow t$, for a relation $\approx$
between target and source contexts.

**Theorem.** There is a compiler between two deterministic languages that satisfies [robust trace equivalence preservation](robust-trace-equivalence-preservation.md),
TP, SCC and CCC, but not [robust safety property preservation](robust-safety-property-preservation.md).

In the witness each run produces one event, the final natural-number result, or silently diverges. A source program is one function
$f(x : \mathrm{Nat}) \mapsto e$ or $f(x : \mathrm{Bool}) \mapsto e$, and a source context is a call $f(n)$ or $f(b)$; a context links with a program only when their argument types agree.
The target language has natural numbers only. The compiler maps $\mathrm{true}, \mathrm{false}$ to $0, 1$, is the identity on natural-number programs, and compiles
$f(x : \mathrm{Bool}) \mapsto e$ to $f(x : \mathrm{Nat}) \mapsto \mathbf{if}\ x < 2\ \mathbf{then}\ e{\downarrow}\ \mathbf{else}\ \mathbf{if}\ x < 3\ \mathbf{then}\ f(2)\ \mathbf{else}\ 42$; it extends to contexts and whole
programs in the evident way. CCC is taken with the relation $\mathbf C_T \approx \mathsf C_S$ iff $\mathbf C_T = \mathsf C_S{\downarrow}$, so CCC and TP follow from SCC. RTEP holds
because two compiled Boolean programs that a target call $f(n)$ distinguishes are distinguished by $f(\mathrm{true})$ or $f(\mathrm{false})$ when $n \in \{0, 1\}$, while for
$n \ge 2$ both diverge or both return $42$, behaviour fixed by the argument type alone. RSP fails: $f(x : \mathrm{Bool}) \mapsto 1$ robustly satisfies "never output $42$",
but its compilation outputs $42$ on input $3$.

## Depends on

- [Robust trace equivalence preservation](robust-trace-equivalence-preservation.md)
- [Robust safety property preservation](robust-safety-property-preservation.md)

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Section 2.1 (TP, SCC and CCC), Section 5, Theorem 5.2 and its proof, and Appendix E.5 (Definitions E.12–E.14, CCC with the linkability condition, Theorem E.15 and Lemmas E.16–E.18).
