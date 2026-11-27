# NP-completeness of the minimum food set problem

**Problems.** Let $(X, \mathcal R, C, F)$ be a catalytic reaction system and $\mathcal R' \subseteq \mathcal R$.

- *min-F generation*: given $\mathcal R'$ that is $F$-generated and an integer $k$, is there $F' \subseteq F$ with $|F'| \le k$ such that $\mathcal R'$ is $F'$-generated (every reactant of every reaction of $\mathcal R'$ lies in $\mathrm{cl}_{\mathcal R'}(F')$)?
- *min-F RAF*: given a RAF set $\mathcal R'$ and $k$, is there $F' \subseteq F$ with $|F'| \le k$ such that $\mathcal R'$ is still a RAF with respect to $F'$?

**Theorem.** Both min-F generation and min-F RAF are NP-complete. Consequently, unless P = NP, there is no polynomial-time algorithm that finds a smallest food set sustaining a given (max)RAF, in contrast to the polynomial-time computation of the maxRAF itself.

## Depends on

- [RAF sets and the maxRAF algorithm](raf-sets-and-the-maxraf-algorithm.md)

## Expansion

Membership in NP holds because closure, and hence $F'$-generation and the RAF property, can be checked in polynomial time. min-F generation reduces to min-F RAF by letting every molecule catalyse every reaction, so it suffices to reduce *exact cover by 3-sets* (X3C) to min-F generation. Given $Y$ with $|Y| = 3q$ and a family $S$ of 3-subsets, use molecules $Y \cup S \cup \{w_s : s \in S\}$, all in the food set, order $Y$ totally, and for each $s = \{a, b, c\}$ with $a < b < c$ add the three reactions

$$s \to a + b + c, \qquad a + b \to w_s, \qquad w_s + c \to s .$$

If $S' \subseteq S$ is an exact cover, starting from $S'$ generates all of $Y$, then every $w_s$, then every $s$, so the $3|S|$ reactions are $S'$-generated with $|S'| = q$. Conversely, any generating $F'$ with $|F'| \le q$ can be replaced by some $S' \subseteq S$ with $|S'| \le |F'|$; since elements of $Y$ are produced only by the splitting reactions, $S'$ must cover $Y$, forcing $|S'| \ge q$ and thus an exact cover. In practice approximately minimal food sets are found by a randomised removal search.

## Sources

- F. L. Sousa, W. Hordijk, M. Steel, W. F. Martin, "Autocatalytic sets in E. coli metabolism", Journal of Systems Chemistry 6 (2015) 4, Results (min-F RAF and min-F generation, Theorem 1; randomised food-set reduction) and Appendix (reduction from X3C), <https://doi.org/10.1186/s13322-015-0009-7> (PMC4429071).
