# Nesterov's general optimal scheme

Let $E$ be a real Hilbert space, $f : E \to \mathbb{R}$ with gradient $\nabla f$ (taken to be $0$ at points where $f$ is not differentiable), and $L, \mu \in \mathbb{R}$. Sequences $\alpha_k, \gamma_k \in \mathbb{R}$ and $x_k, y_k, v_k \in E$ follow **Nesterov's general scheme** if $\gamma_0 > 0$, $v_0 = x_0$, and for every $k$:

1. $\alpha_k \in (0, 1]$ solves $L\alpha_k^2 = (1 - \alpha_k)\gamma_k + \alpha_k \mu$, and $\gamma_{k+1} = (1 - \alpha_k)\gamma_k + \alpha_k\mu$;
2. $(\gamma_k + \alpha_k \mu)\, y_k = \alpha_k \gamma_k v_k + \gamma_{k+1} x_k$;
3. $f(x_{k+1}) \le f(y_k) - \dfrac{1}{2L}\|\nabla f(y_k)\|^2$ (with $\frac{1}{0} = 0$);
4. $\gamma_{k+1}\, v_{k+1} = (1 - \alpha_k)\gamma_k v_k + \alpha_k \mu y_k - \alpha_k \nabla f(y_k)$.

In the source's setting, $f$ differentiable with $L > 0$ and $\mu \ge 0$, every $\gamma_k$ and $\gamma_k + \alpha_k\mu$ is positive, and steps 2 and 4 are the source's formulas $y_k = \frac{\alpha_k \gamma_k v_k + \gamma_{k+1} x_k}{\gamma_k + \alpha_k \mu}$ and $v_{k+1} = \frac{(1 - \alpha_k)\gamma_k v_k + \alpha_k \mu y_k - \alpha_k \nabla f(y_k)}{\gamma_{k+1}}$, multiplied by their denominators. Step 3 holds for the gradient step $x_{k+1} = y_k - \nabla f(y_k)/L$ when $\nabla f$ is $L$-Lipschitz (Constant Step Scheme I, (2.2.7), of the source); the scheme leaves the choice of $x_{k+1}$ free. The source asks $\alpha_k \in (0, 1)$; the definition here also allows $\alpha_k = 1$, which only enlarges the class of sequences covered by the theorems below.

The point $v_k$ is the minimiser of the estimate function $\varphi_k(x) = \varphi_k^* + \frac{\gamma_k}{2}\|x - v_k\|^2$ of Lemma 2.2.3 of the source, built recursively from the linear (or quadratic, when $\mu > 0$) models $f(y_k) + \langle \nabla f(y_k), x - y_k\rangle + \frac{\mu}{2}\|x - y_k\|^2$, which are lower bounds for $f$ when $f$ is convex and differentiable with $\mu$-strong convexity ($\mu = 0$: plain convexity); the choice of $y_k$ is what makes $f(x_{k+1}) \le \varphi_{k+1}^*$ follow from step 3.

## Background

- [Sufficient decrease of a gradient step](../gradient-descent/gradient-descent-sufficient-decrease.md): the gradient step $1/L$ satisfies the descent condition of step 3.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.2.1: Definition 2.2.1 (estimate sequences), Lemmas 2.2.2 and 2.2.3, and the General scheme (2.2.6), which defines these sequences.
