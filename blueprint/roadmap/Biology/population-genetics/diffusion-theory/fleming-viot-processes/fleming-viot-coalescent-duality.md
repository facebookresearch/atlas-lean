# Duality between Fleming–Viot processes and coalescents

Let $E$ be a type space with a mutation operator $B$ (each lineage mutates at rate $\theta/2$). The Fleming–Viot process $(Z_t)$ with mutation operator $B$, a process with values in the probability measures on $E$, solves the martingale problem whose generator acts on $F_f(\mu) = \langle f, \mu^{\otimes n}\rangle$, $f$ bounded measurable on $E^n$, by $\mathcal{A}F_f(\mu) = \langle Af, \mu^{\otimes n}\rangle$ with

$$Af = \sum_{i=1}^n B_if + \sum_{1 \le i < j \le n}\bigl(\Phi_{ij}f - f\bigr),$$

where $B_i$ applies $B$ to the $i$-th input and $\Phi_{ij}$ identifies the $i$-th and $j$-th inputs (Ethier and Kurtz 1993). Any solution satisfies the moment duality

$$E\bigl[\langle\zeta_0, Z_t^{\otimes n}\rangle\bigr] = E\bigl[\langle\zeta_t, Z_0^{\otimes|R^{(n)}_t|}\rangle\bigr], \qquad t \ge 0,$$

where $(\zeta_t)$ is the function-valued dual started from $\zeta_0 = f$, in which each pair of inputs is identified at rate $1$ and each input is acted on by $B$, and $|R^{(n)}_t|$ is its number of inputs, the block count of a Kingman coalescent started from $n$ blocks (Dawson and Hochberg 1982; Ethier and Kurtz 1993; for the genealogical interpretation, Donnelly and Kurtz 1996). The duality gives uniqueness in law for the martingale problem (Ethier and Kurtz 1993). For a compact type space and a bounded jump-type mutation operator that uniqueness is [Fleming–Viot uniqueness by moment duality](fleming-viot-uniqueness-by-function-valued-coale.md), and for finitely many types the identification with the multi-allele Wright–Fisher diffusion is the [finite-type correspondence](finite-type-fleming-viot-k-allele-wright-fisher.md); neither is claimed here. The target is the moment duality, with its Kingman block-counting dual, and, as a separate statement, uniqueness for mutation operators and type spaces outside the compact, bounded case.

## Depends on

- [Generator of Kingman's block-counting process](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md)

## Expansion

1. The generator on functions $\mu \mapsto \langle f, \mu^{\otimes n}\rangle$ and the operators $B_i$ and $\Phi_{ij}$.
2. The function-valued dual process and the identity $\mathcal{A}F_f(\mu) = \langle Af, \mu^{\otimes n}\rangle$.
3. The moment duality, by the generator identity and a duality argument.
4. Uniqueness of the martingale problem by duality, beyond the compact type space with bounded mutation operator treated on the linked uniqueness page.
5. The analogous duality between $\Lambda$-Fleming–Viot processes and $\Lambda$-coalescents, as a separate statement.

## Sources

- S. N. Ethier and T. G. Kurtz, Fleming–Viot processes in population genetics, SIAM J. Control Optim. 31 (1993), 345–386. <https://doi.org/10.1137/0331019>
- D. A. Dawson and K. J. Hochberg, Wandering random measures in the Fleming–Viot model, Ann. Probab. 10 (1982), 554–580.
- P. Donnelly and T. G. Kurtz, A countable representation of the Fleming–Viot measure-valued diffusion, Ann. Probab. 24 (1996), 698–742.
