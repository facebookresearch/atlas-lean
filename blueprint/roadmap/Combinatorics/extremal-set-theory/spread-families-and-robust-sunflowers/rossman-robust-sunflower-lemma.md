# Rossman's robust sunflower lemma and monotone clique lower bounds

For $0 < \alpha < 1$ and $0 < \beta \le 1/e$, every $\ell$-uniform family of more than $\ell!\,(C\log(1/\beta)/\alpha)^{\ell}$ sets, for an absolute constant $C$, contains an $(\alpha, \beta)$-robust sunflower (Rossman). For $\ell \ge 2$ and $0 < \alpha, \beta < 1$, Rao, building on Alweiss-Lovett-Wu-Zhang, improves the threshold to $(C\log(\ell/\beta)/\alpha)^{\ell}$. Robust sunflowers replace sunflowers in Razborov's approximation method, yielding average-case monotone circuit lower bounds: for fixed $k \ge 3$, a threshold $p = \Theta(n^{-2/(k-1)})$ for containing a $k$-clique and $p^{+} = p + p^{1+1/k^2}$, monotone circuits of size $O(n^{k/4})$ cannot solve $k$-clique with high probability on both $G(n, p)$ and $G(n, p^{+})$.

## Proof sketch

Rossman's bound follows from Janson's inequality applied inside links of maximal size, in the style of the Erdős-Rado induction. The spread-lemma bound follows by passing to a spread link and applying the spread lemma with density $\alpha$ and failure probability $\beta$.

## Depends on

- [Robust sunflowers](robust-sunflowers-and-satisfying-systems.md)

## Proof depends on

- [Spread lemma: random sets of moderate density contain members of spread families](spread-lemma-random-sets-contain-members-of-spread-families.md)
- [Sunflower-free families have spread links](sunflower-free-families-have-spread-restrictions.md)

## Sources

- Benjamin Rossman, "The monotone complexity of k-clique on random graphs", SIAM Journal on Computing 43(1) (2014) 256-279, FOCS (2010), Theorems 1.2 and 4.4.
- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483, Theorem 1.9 and Section 4 (which states Rao's bound for robust sunflowers).
- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774.
