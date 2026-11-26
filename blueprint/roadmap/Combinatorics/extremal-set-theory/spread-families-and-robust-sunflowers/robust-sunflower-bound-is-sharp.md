# The robust sunflower bound is sharp up to lower-order terms

For every sufficiently large $\ell$ there is an $\ell$-uniform family of at least $\big((\log_2 \ell)/8\big)^{\ell - \sqrt{\ell}} = (\log \ell)^{\ell(1 - o(1))}$ sets that contains no $(1/2, 1/2)$-robust sunflower. Hence, for fixed $\alpha, \beta$, the threshold $(C\log(\ell/\beta)/\alpha)^{\ell} = (\log \ell)^{\ell(1 + o(1))}$ above which every $\ell$-uniform family contains an $(\alpha, \beta)$-robust sunflower cannot be lowered to $(\log \ell)^{\ell(1 - \eta)}$ for any constant $\eta > 0$.

## Proof sketch

Let $\varepsilon = 1/\sqrt{\ell}$, take pairwise disjoint blocks $X_1, \dots, X_\ell$ of size $m = \log_2(\varepsilon \ell)$, and let $\hat{\mathcal{F}}$ be the family of sets with exactly one element in each block. Greedily choose $\mathcal{F} \subseteq \hat{\mathcal{F}}$ with $|S \cap S'| \le (1 - \varepsilon)\ell$ for all distinct $S, S' \in \mathcal{F}$; this keeps $|\mathcal{F}| \ge 2^{-\ell} m^{(1-\varepsilon)\ell} \ge \big((\log_2 \ell)/8\big)^{\ell - \sqrt{\ell}}$. A robust sunflower in $\mathcal{F}$ with kernel $K$ has two distinct members containing $K$, so $|K| \le (1 - \varepsilon)\ell$ and at least $\varepsilon\ell$ blocks are disjoint from $K$. A random set $W$ of density $1/2$ misses one of these blocks with probability at least $1 - (1 - 2^{-m})^{\varepsilon\ell} \ge 1 - 1/e > 1/2$, and then $W$ contains no $S \setminus K$ with $S \in \mathcal{F}$.

## Depends on

- [Robust sunflowers](robust-sunflowers-and-satisfying-systems.md)
- [Rossman's robust sunflower lemma and monotone clique lower bounds](rossman-robust-sunflower-lemma.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483, Lemma 3.1.
