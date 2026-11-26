# Generalized kinship boundary values for inbred founders

For pedigree members $a, b, c, d$ (not necessarily distinct) let $\phi_{abc}$ and $\phi_{abcd}$ be the probabilities that one allele sampled at random from each listed individual at an autosomal locus are all identical by descent (IBD), and let $\phi_{ab,cd}$ be the probability that, sampling one allele from each, the alleles from $a$ and $b$ are IBD and the alleles from $c$ and $d$ are IBD. Karigl's recursions over a nonfounder $a$ with parents $p, m$ (and $b, c, d$ nondescendants of $a$), for example

$$\phi_{abc} = \tfrac12(\phi_{pbc} + \phi_{mbc}), \quad \phi_{aaa} = \tfrac14(1 + 3\phi_{pm}), \quad \phi_{aaaa} = \tfrac18(1 + 7\phi_{pm}), \quad \phi_{ab,ac} = \tfrac14(2\phi_{abc} + \phi_{pb,mc} + \phi_{mb,pc}),$$

are unchanged when founders may be inbred (Eq. (3)). Distinct founders are unrelated, so $\phi_{ab} = \phi_{abc} = \phi_{abcd} = \phi_{ab,cd} = 0$ for distinct founders $a, b$ (Eq. (4)). Only the founder boundary values change: for founders $a, b$ with inbreeding coefficients $f_a, f_b$ (Eq. (6)),

$$\phi_{aaa} = \tfrac14(1 + 3f_a), \quad \phi_{aaaa} = \tfrac18(1 + 7f_a), \quad \phi_{aa,aa} = \tfrac14(1 + 3f_a), \quad \phi_{aa,bb} = \tfrac14(1 + f_a)(1 + f_b).$$

With $f_a = f_b = 0$ these reduce to the outbred values $\tfrac14, \tfrac18, \tfrac14, \tfrac14$ (Eq. (5)). The nine condensed Jacquard identity coefficients are a linear function of these generalized kinship coefficients, so they can be computed in pedigrees with inbred founders.

## Depends on

- [Inbreeding coefficient under gene dropping](inbreeding.md)
- [Kinship coefficient by Malécot's recursion](kinship.md)

## Proof depends on

- [Inbreeding coefficient under gene dropping](inbreeding.md)
- [Kinship coefficient by Malécot's recursion](kinship.md)

## Expansion

Condition on the event $A$ that founder $a$ is autozygous, of probability $f_a$. Three alleles sampled with replacement from $a$ are IBD with probability $1$ on $A$, and with probability $\tfrac14$ off $A$ (all three draws hit the same one of two non-IBD alleles), giving $f_a + \tfrac14(1 - f_a) = \tfrac14(1 + 3f_a)$. The other values follow the same way; $\phi_{aa,bb}$ factors because distinct founders are independent and each factor is $\phi_{aa} = \tfrac12(1 + f_a)$ (Section 3.1).

## Sources

- M. D. Vigeland, Relatedness coefficients in pedigrees with inbred founders, Journal of Mathematical Biology 81 (2020), 185-207. <https://doi.org/10.1007/s00285-020-01505-x> (PMCID PMC7363742)
