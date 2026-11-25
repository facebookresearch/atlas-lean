# Feedback linearization of single-input systems

Let $X \subseteq \mathbb{R}^n$ be open, let $f, g : X \to \mathbb{R}^n$ be smooth, and consider $\dot x = f(x) + u\,g(x)$ with $u \in \mathbb{R}$. For smooth vector fields write $[X, Y] = DY\,X - DX\,Y$, $\mathrm{ad}_f^0 g = g$ and $\mathrm{ad}_f^{k+1} g = [f, \mathrm{ad}_f^k g]$. The system is **feedback linearizable about** $x_0 \in X$ if there are an open $O \ni x_0$, a diffeomorphism $T$ of $O$ onto an open subset of $\mathbb{R}^n$, smooth $\alpha, \beta : O \to \mathbb{R}$ with $\beta$ nowhere zero, and a controllable single-input linear system $\dot z = Az + vb$, such that the change of variables $z = T(x)$, $v = (u - \alpha(x))/\beta(x)$ carries the solutions of the system in $O$ onto the solutions of $\dot z = Az + vb$.

**Theorem.** The system is feedback linearizable about $x_0$ if and only if

1. the vectors $g(x_0), \mathrm{ad}_f g(x_0), \dots, \mathrm{ad}_f^{n-1} g(x_0)$ are linearly independent, and
2. the distribution $\Delta_{n-1}$ spanned by $g, \mathrm{ad}_f g, \dots, \mathrm{ad}_f^{n-2} g$ is involutive on some neighborhood of $x_0$: the bracket of any two of these fields lies pointwise in their span.

For $n = 1$ the condition is $g(x_0) \ne 0$. Both conditions are unchanged if the bracket is defined with the opposite sign.

## Expansion

Necessity is a computation: brackets transform naturally under the diffeomorphism $T$, the feedback changes $f$ to $f + \alpha g$ and $g$ to $\beta g$, which preserves the spans of the first $k$ iterated brackets for each $k$, and for the controller form $(A_n, b_n)$ the iterated brackets are, up to sign, the constant vectors $b_n, A_nb_n, \dots, A_n^{n-1}b_n$, which are linearly independent and span involutive constant distributions. For sufficiency, Frobenius' theorem applied to the involutive distribution $\Delta_{n-1}$ of constant rank $n - 1$ gives a smooth $\varphi$ near $x_0$ whose differential annihilates $\Delta_{n-1}$ and, by condition 1, does not annihilate $\mathrm{ad}_f^{n-1} g$; then $T = (\varphi, L_f\varphi, \dots, L_f^{n-1}\varphi)$, $\beta = 1/(L_gL_f^{n-1}\varphi)$ and $\alpha = -\beta L_f^n\varphi$ give the controller form. Beyond Lie brackets of vector fields, the prerequisite is Frobenius' theorem.

## Background

- [Iterated Lie brackets of a family of vector fields](iterated-lie-brackets.md): brackets of vector fields

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 5.3: feedback equivalence and Definition 5.3.2 (feedback linearizable about $x_0$, p. 199), Lemma 5.3.5 (equivalence to the controller form $(A_n, b_n)$) and Theorem 15 (feedback linearizable if and only if $g(x_0), \mathrm{ad}_f g(x_0), \dots, \mathrm{ad}_f^{n-1} g(x_0)$ are linearly independent and $\Delta_{n-1}$ is involutive near $x_0$, p. 200), with the proof by Frobenius' theorem.
