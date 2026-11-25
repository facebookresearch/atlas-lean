# Lyapunov's direct method and Lyapunov's instability theorem

Let $D \subseteq \mathbb{R}^n$ be open, $f : D \to \mathbb{R}^n$ locally Lipschitz, and $x_0 \in D$ an equilibrium, $f(x_0) = 0$, of $\dot x = f(x)$. For a continuously differentiable $V$ write $\dot V(x) = \nabla V(x) \cdot f(x)$.

1. **Stability and asymptotic stability.** Let $B \subseteq D$ be an open ball around $x_0$ and $V : B \to \mathbb{R}$ continuously differentiable with $V(x_0) = 0$ and $V(x) > 0$ for $x \ne x_0$. If $\dot V \le 0$ on $B$, then $x_0$ is stable: for every $\varepsilon > 0$ there is $\delta > 0$ such that solutions starting within $\delta$ of $x_0$ exist for all $t \ge 0$ and stay within $\varepsilon$. If moreover $\dot V(x) < 0$ for every $x \in B \setminus \{x_0\}$, then $x_0$ is asymptotically stable: in addition, solutions starting close enough to $x_0$ converge to $x_0$.
2. **Instability.** Let $V : B \to \mathbb{R}$ be continuously differentiable on an open ball $B$ around $x_0$, and suppose there is $c > 0$ with $\dot V(x) - cV(x) \ge 0$ for all $x \in B$, and that $x_0$ lies in the closure of $\{x \in B : V(x) > 0\}$. Then $x_0$ is unstable: there is $\varepsilon > 0$ such that for every $\delta > 0$ some solution starting within $\delta$ of $x_0$ leaves the $\varepsilon$-ball.

Part 1 requires a strict decrease off the equilibrium for convergence; with only $\dot V \le 0$, LaSalle's invariance principle is the tool. In part 2, $V$ need not be positive anywhere but near $x_0$, and no sign of $V(x_0)$ is assumed.

**Proof.** For part 1, choose $r > 0$ with the closed ball $\bar B_r(x_0) \subseteq B$ and let $m = \min\{V(x) : \|x - x_0\| = r\} > 0$. Given $\varepsilon \le r$, replace $r$ by $\varepsilon$ and choose $\delta$ with $V < m$ on $B_\delta(x_0)$. A solution from $B_\delta$ has $V(x(t))$ nonincreasing while it stays in $B$, so it never reaches the sphere of radius $\varepsilon$; staying in a compact set, it exists for all $t \ge 0$. If $\dot V < 0$ off $x_0$, $V(x(t))$ decreases to a limit $\ell \ge 0$; if $\ell > 0$, the solution stays in the compact set $\{\ell \le V\} \cap \bar B_\varepsilon(x_0)$, where $\dot V \le -\eta < 0$, so $V(x(t)) \le V(x(0)) - \eta t \to -\infty$, a contradiction. So $V(x(t)) \to 0$, which forces $x(t) \to x_0$ by positivity and compactness. For part 2, let $\beta$ bound $|V|$ on a smaller closed ball $\bar B_\varepsilon(x_0) \subseteq B$. Given $\delta$, pick $x$ within $\delta$ of $x_0$ with $V(x) > 0$. If its solution stayed in $\bar B_\varepsilon$ for all $t \ge 0$, then $\alpha(t) = e^{-ct}V(x(t))$ would satisfy $\dot\alpha = e^{-ct}(\dot V - cV)(x(t)) \ge 0$, so $V(x(t)) \ge e^{ct}V(x) \to \infty$, contradicting $V \le \beta$.

## Background

- [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md): convergence when $\dot V$ is only nonpositive
- [Lyapunov's indirect method, instability](../lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md): instability from the linearization

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 5.7: Definition 5.7.1 (Lyapunov functions: proper and positive definite near $x_0$, decreasing along solutions, p. 219), Theorem 17 (a Lyapunov function gives asymptotic stability, pp. 220–222), Lemma 5.7.4 (the strict inequality $\nabla V(x) \cdot f(x) < 0$ off $x_0$ suffices, p. 224), and Theorem 20 (instability from $L_f V - cV \ge 0$ with $x_0$ in the closure of $\{V > 0\}$, pp. 237–238). The elementary proofs are written out on the page.
