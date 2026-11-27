# Duality between Fleming–Viot processes and coalescents

Let the type space $E$ be a locally compact separable metric space and let the mutation operator $B$ generate a Feller semigroup on $E$ (for example, each lineage mutates at rate $\theta/2$ by a jump kernel), and let $B^{(n)}$ be the generator of the product semigroup on $E^n$, so that $B^{(n)}f = \sum_{i=1}^n B_if$ on product functions. The Fleming–Viot process $(Z_t)$ with mutation operator $B$, a process with values in the probability measures on $E$, solves the [martingale problem](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md) whose generator acts on $F_f(\mu) = \langle f, \mu^{\otimes n}\rangle$, $f \in \mathcal D(B^{(n)})$, by $\mathcal{A}F_f(\mu) = \langle Af, \mu^{\otimes n}\rangle$ with

$$Af = B^{(n)}f + \sum_{1 \le i < j \le n}\bigl(\Phi_{ij}f - f\bigr),$$

where $B_i$ applies $B$ to the $i$-th input and $\Phi_{ij}$ identifies the $i$-th and $j$-th inputs (Ethier and Kurtz 1993; Ethier and Kurtz 1998, eq. (1.9) with no selection or recombination). Any solution $Z$ satisfies, for every bounded measurable $f$ on $E^n$, the moment duality

$$E\bigl[\langle\zeta_0, Z_t^{\otimes n}\rangle\bigr] = E\bigl[\langle\zeta_t, Z_0^{\otimes|R^{(n)}_t|}\rangle\bigr], \qquad t \ge 0,$$

where $(\zeta_t)$ is the function-valued dual started from $\zeta_0 = f$ and independent of $Z$, in which each pair of inputs is identified at rate $1$ and each input is acted on by $B$, and $|R^{(n)}_t|$ is its number of inputs, the block count of a Kingman coalescent started from $n$ blocks (Dawson and Hochberg 1982; Ethier and Kurtz 1993; Ethier and Kurtz 1998, eqs. (2.1)–(2.5), who credit the identity (2.5) to Ethier and Kurtz 1987; for the genealogical interpretation, Donnelly and Kurtz 1996). The duality gives uniqueness in law for the martingale problem (Ethier and Kurtz 1993; Ethier and Kurtz 1998, Theorem 1.1 and the argument after (2.5)). For a compact type space and a bounded jump-type mutation operator that uniqueness is [Fleming–Viot uniqueness by moment duality](fleming-viot-uniqueness-by-function-valued-coale.md), and for finitely many types the identification with the multi-allele Wright–Fisher diffusion is the [finite-type correspondence](finite-type-fleming-viot-k-allele-wright-fisher.md); neither is claimed here. The target is the moment duality, with its Kingman block-counting dual, and, as a separate statement, uniqueness for mutation operators and type spaces outside the compact, bounded case.

## Depends on

- [Martingale problems](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Generator of Kingman's block-counting process](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)

## Expansion

1. The generator on functions $\mu \mapsto \langle f, \mu^{\otimes n}\rangle$, $f \in \mathcal D(B^{(n)})$, and the operators $B^{(n)}$, $B_i$ and $\Phi_{ij}$.
2. The function-valued dual process and the identity $\mathcal{A}F_f(\mu) = \langle Af, \mu^{\otimes n}\rangle$.
3. The moment duality for a dual independent of $Z$, by the generator identity and a duality argument.
4. Uniqueness of the martingale problem by duality, beyond the compact type space with bounded mutation operator treated on the linked uniqueness page.
5. The analogous duality between $\Lambda$-Fleming–Viot processes and $\Lambda$-coalescents, as a separate statement.

## Sources

- S. N. Ethier and T. G. Kurtz, Fleming–Viot processes in population genetics, SIAM J. Control Optim. 31 (1993), 345–386. <https://doi.org/10.1137/0331019>
- S. N. Ethier and T. G. Kurtz, Coupling and ergodic theorems for Fleming–Viot processes, Ann. Probab. 26(2) (1998), 533–561, eq. (1.9) (the generator), Theorem 1.1 (uniqueness for the martingale problem), and eqs. (2.1)–(2.5) (the function-valued dual and the moment duality, credited there to Ethier and Kurtz 1987). Open access at Project Euclid. <https://doi.org/10.1214/aop/1022855643>
- D. A. Dawson and K. J. Hochberg, Wandering random measures in the Fleming–Viot model, Ann. Probab. 10 (1982), 554–580.
- P. Donnelly and T. G. Kurtz, A countable representation of the Fleming–Viot measure-valued diffusion, Ann. Probab. 24 (1996), 698–742.
