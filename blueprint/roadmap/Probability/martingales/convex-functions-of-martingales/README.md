# Convex functions of martingales

Let $\mu$ be a probability measure, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration, and let $(X_n)_{n \in \mathbb{N}}$ be a real-valued martingale with respect to $(\mathcal{F}_n)$ and $\mu$. If $\varphi : \mathbb{R} \to \mathbb{R}$ is convex and $\varphi(X_n)$ is integrable for every $n$, then $(\varphi(X_n))_{n \in \mathbb{N}}$ is a submartingale with respect to $(\mathcal{F}_n)$ and $\mu$.

## Idea

The proof is the conditional Jensen inequality: for $m \le n$,

$$\mathbb{E}[\varphi(X_n) \mid \mathcal{F}_m] \ge \varphi(\mathbb{E}[X_n \mid \mathcal{F}_m]) = \varphi(X_m).$$

So $|X_n|$, $X_n^+$, and $X_n^2$ or $e^{t X_n}$ when they are integrable, are submartingales. This is how maximal inequalities and convergence theorems proved for submartingales apply to martingales, as in Doob's maximal inequality for $|X_n|$. Integrability of $\varphi(X_n)$ must be assumed, since a submartingale is integrable by definition. The card also holds two forms of the statement: a concave function of a martingale is a supermartingale, and a convex nondecreasing function of a submartingale is again a submartingale. Monotonicity is needed there: $(x - 4)^2$ decreases along the deterministic submartingale $2, 3$.

## Statements

- [Convex functions of martingales are submartingales](submartingale-comp-convex.md)
- [Concave functions of martingales are supermartingales](supermartingale-comp-concave.md): dual statement for concave functions
- [Convex nondecreasing functions preserve submartingales](comp-convex-of-monotone-on.md): submartingale version, nondecreasing convex functions
