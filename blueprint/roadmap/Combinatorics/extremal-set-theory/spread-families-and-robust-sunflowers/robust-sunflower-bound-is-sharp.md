# The robust sunflower bound is sharp up to lower-order terms

For all $\alpha, \beta \in (0, 1/2)$ and $\ell \ge 1$ there are $\ell$-uniform families of size $\big(c\log(1/\beta)/\alpha\big)^{\ell}$, for an absolute constant $c > 0$, containing no $(\alpha, \beta)$-robust sunflower. Hence the Alweiss-Lovett-Wu-Zhang bound $(C\log(\ell/\beta)/\alpha)^{\ell}$ for robust sunflowers is optimal up to the dependence on $\log\ell$, and further progress toward the Erdős-Rado conjecture must exploit genuine sunflowers rather than robustness alone.

## Proof sketch

Take the $\ell$-fold product of a family of $m$ disjoint blocks: sets choosing one element from each of $\ell$ blocks, each block of size $s = c\log(1/\beta)/\alpha$. A random set $W$ of density $\alpha$ contains a member if and only if it meets every block, and it misses a fixed block with probability $(1-\alpha)^{s} \ge \beta^{c'}$ for a constant $c' < 1$ when $c$ is small. Hence $W$ contains no member with probability at least $\beta^{c'} > \beta$, and the same computation applies to every subfamily after removing its kernel, so no subfamily is an $(\alpha, \beta)$-robust sunflower.

## Depends on

- [Robust sunflowers](robust-sunflowers-and-satisfying-systems.md)
- [Rossman's robust sunflower lemma and monotone clique lower bounds](rossman-robust-sunflower-lemma.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
