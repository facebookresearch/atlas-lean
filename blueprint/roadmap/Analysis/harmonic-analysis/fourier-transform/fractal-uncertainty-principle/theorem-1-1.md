# Cohen's fractal uncertainty principle for line-porous sets

Let $d$ be a natural number and
$\nu > 0$. Then there are real numbers $\beta > 0$ and $C > 0$ such that for every $h$ with
$0 < h < 1/100$ and all measurable sets $X, Y$ in the Euclidean space $\mathbb{R}^d$ the following
holds: if $X \subseteq [-1,1]^d$ is $\nu$-porous on balls from scales $h$ to $1$ and
$Y \subseteq [-h^{-1},h^{-1}]^d$ is $\nu$-porous on lines from scales $1$ to $h^{-1}$, then every
$f \in L^2(\mathbb{R}^d)$ whose Fourier transform $\mathcal{F}f$ vanishes almost everywhere outside
$Y$ satisfies $\|\mathbf{1}_X f\|_2 \le C h^{\beta} \|f\|_2$. Thus $\beta$ and $C$ depend only on
$\nu$ and $d$.

Here $\mathcal{F}$ is the Fourier transform on $L^2(\mathbb{R}^d)$, extended by continuity from
$\mathcal{F}f(\xi) = \int_{\mathbb{R}^d} e^{-2\pi i \langle x, \xi \rangle} f(x)\,dx$ on Schwartz
functions.

We require $X$ and $Y$ to be measurable to make the statement more natural.

## Sources

- A. Cohen, `Fractal uncertainty in higher dimensions`, Annals of Math, 202 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_fractal_uncertainty` of the lean-eval benchmark.
