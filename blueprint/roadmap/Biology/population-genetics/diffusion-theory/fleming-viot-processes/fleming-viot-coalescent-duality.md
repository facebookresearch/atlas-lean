# Duality between Fleming–Viot processes and coalescents

Let $E$ be a type space with a mutation operator $B$ (each lineage mutates at rate $\theta/2$). The Fleming–Viot process $(Z_t)$ with mutation operator $B$, a process with values in the probability measures on $E$, solves the martingale problem whose generator acts on $F_f(\mu) = \langle f, \mu^{\otimes n}\rangle$, $f$ bounded measurable on $E^n$, by $\mathcal{A}F_f(\mu) = \langle Af, \mu^{\otimes n}\rangle$ with
$$Af = \sum_{i=1}^n B_if + \sum_{1 \le i < j \le n}\bigl(\Phi_{ij}f - f\bigr),$$
where $B_i$ applies $B$ to the $i$-th input and $\Phi_{ij}$ identifies the $i$-th and $j$-th inputs (Birkner, eq. (1.44)). Any solution satisfies the moment duality
$$E\bigl[\langle\zeta_0, Z_t^{\otimes n}\rangle\bigr] = E\bigl[\langle\zeta_t, Z_0^{\otimes|R^{(n)}_t|}\rangle\bigr], \qquad t \ge 0,$$
where $(\zeta_t)$ is the function-valued dual started from $\zeta_0 = f$, in which each pair of inputs is identified at rate $1$ and each input is acted on by $B$, and $|R^{(n)}_t|$ is its number of inputs, the block count of a Kingman coalescent started from $n$ blocks (Birkner, Proposition 1.5.9). The duality gives uniqueness in law for the martingale problem (Birkner, Theorem 1.5.8). For finitely many types the process is the multi-allele Wright–Fisher diffusion on the simplex (Birkner, Remark 1.5.10). The target is the duality and the uniqueness argument as separate statements.

## Expansion

1. The generator on functions $\mu \mapsto \langle f, \mu^{\otimes n}\rangle$ and the operators $B_i$ and $\Phi_{ij}$.
2. The function-valued dual process and the identity $\mathcal{A}F_f(\mu) = \langle Af, \mu^{\otimes n}\rangle$.
3. The moment duality, by the generator identity and a duality argument.
4. Uniqueness of the martingale problem by duality.
5. The analogous duality between $\Lambda$-Fleming–Viot processes and $\Lambda$-coalescents, as a separate statement.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Sec. 1.5: eq. (1.44), Theorem 1.5.8, Proposition 1.5.9 and Remark 1.5.10.
