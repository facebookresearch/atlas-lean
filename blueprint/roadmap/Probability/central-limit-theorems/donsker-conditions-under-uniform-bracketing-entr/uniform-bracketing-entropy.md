# Uniform bracketing entropy

Let $S$ be a measurable space, $(F_i)_{i \in \iota}$ a family of real functions on $S$ and $\varepsilon \in \mathbb{R}$. The uniform bracketing entropy is the extended nonnegative real

$$H(\varepsilon) = \inf\Big\{ \sqrt{\log n} : n \in \mathbb{N},\ F \text{ has a uniform bracket cover of width } \varepsilon \text{ with } n \text{ brackets} \Big\} \in [0, \infty],$$

where a uniform bracket cover consists of measurable $l_j \le u_j$ with $u_j - l_j \le \varepsilon$ pointwise such that each $F_i$ satisfies $l_j \le F_i \le u_j$ for some $j$, and $\log 0 = 0$. It equals $\sqrt{\log N_{[\,]}(\varepsilon, F, \lVert \cdot \rVert_\infty)}$ when a finite cover exists and is $\infty$ when none does.
