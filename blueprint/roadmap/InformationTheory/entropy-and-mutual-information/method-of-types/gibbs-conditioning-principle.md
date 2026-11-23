# Gibbs' conditioning principle (finite alphabet)

Let $Q > 0$ be a distribution on a finite alphabet and $\Gamma$ a set of distributions satisfying
(III.21) in the explicit form of [Sanov's theorem for finite alphabets](sanov-theorem-for-finite-alphabets.md):
$r \le D(P\|Q)$ on $\Gamma$, and $n$-types $s_n$, in $\Gamma$ for all large $n$, with
$D(P_{s_n}\|Q) \to r$. Since $Q > 0$, $D(\Gamma\|Q) < \infty$ for nonempty $\Gamma$, so this form is
equivalent to (III.21), and $r = D(\Gamma \| Q)$. If a unique $P^*$ in the closure of $\Gamma$ has $D(P^* \| Q) = r$, then for
every $k$ and every word $y$ of length $k$,

$$\frac{Q^n\{x : P_x \in \Gamma,\ x_0 \dots x_{k-1} = y\}}{Q^n\{x : P_x \in \Gamma\}} \longrightarrow \prod_{i<k} P^*(y_i),$$

that is, conditioned on the rare event $P_x \in \Gamma$, the first $k$ draws are asymptotically
i.i.d. with law $P^*$. It is weaker than the source in one respect: it assumes $Q > 0$, while Csiszár allows any $Q$.

## Background

- [I-projection: support and Pythagorean inequality](../../information-inequalities/i-projections/pythagorean-inequality-for-i-projections.md):
  when $\Gamma$ is convex, $P^*$ is the I-projection of $Q$ on the closure of $\Gamma$, and the
  Pythagorean inequality is the step of the classical proof that forces types near the minimum to
  concentrate near $P^*$.

## Sources

- I. Csiszár, "The method of types", *IEEE Trans. Inform. Theory* 44(6) (1998), 2505–2523, Corollary to Theorem III.3.
- I. Csiszár, "Sanov property, generalized I-projection and a conditional limit theorem",
  *Ann. Probab.* 12 (1984), 768–793: the general version; not consulted for this statement.
