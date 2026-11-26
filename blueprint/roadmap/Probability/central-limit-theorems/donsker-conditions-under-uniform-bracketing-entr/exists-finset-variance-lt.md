# Total boundedness of a class with finite uniform bracketing entropy

Let $\mu$ be a probability measure on a measurable space $S$ and $(F_i)_{i \in \iota}$ measurable functions $S \to \mathbb{R}$ whose uniform bracketing entropy integral is finite,

$$\int_{(0,1]} H(\varepsilon) \, d\varepsilon < \infty,$$

where $H(\varepsilon) \in [0, \infty]$ is the [uniform bracketing entropy](uniform-bracketing-entropy.md), the infimum of $\sqrt{\log n}$ over the sizes $n$ of uniform bracket covers of width $\varepsilon$, with $\log 0 = 0$; for instance the empty family has a cover by zero brackets, so its entropy is $0$.

Then for every $\delta > 0$ there is a finite set $s \subseteq \iota$ such that every $i \in \iota$ has some $j \in s$ with

$$\mathrm{Var}_\mu[F_i - F_j] < \delta^2.$$

Here $\mathrm{Var}_\mu[f]$ is the real part of the extended variance; since $\mu$ is a probability measure and each $F_i - F_j$ is measurable, $\mathrm{Var}_\mu[F_i - F_j]$ is $0$ when $F_i - F_j \notin L^2(\mu)$. When every $F_i$ is in $L^2(\mu)$, this says that $F$ is totally bounded in the standard-deviation semimetric $\rho_\mu(f, g) = \sqrt{\mathrm{Var}_\mu[f - g]}$.
