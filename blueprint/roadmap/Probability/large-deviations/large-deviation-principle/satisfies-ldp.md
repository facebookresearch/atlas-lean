# Large deviation principle for a sequence of measures

Let $X$ be a topological space with
a $\sigma$-algebra containing every open set, let $(\mu_n)_{n \in \mathbb{N}}$ be a sequence of
measures on $X$, and let $I : X \to [0, \infty]$. The sequence $(\mu_n)$ satisfies the large
deviation principle with rate function $I$ and speed $n$ if $I$ is a rate function, every open
set $U \subseteq X$ satisfies

$$\liminf_{n \to \infty} \frac{1}{n} \log \mu_n(U) \ge -\inf_{x \in U} I(x),$$

and every closed set $F \subseteq X$ satisfies

$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(F) \le -\inf_{x \in F} I(x).$$

Here $\log 0 = -\infty$, an infimum over the empty set is $\infty$, and the limits are taken in
the extended reals.
