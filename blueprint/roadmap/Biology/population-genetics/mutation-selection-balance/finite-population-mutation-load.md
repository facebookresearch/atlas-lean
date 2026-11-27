# Mutation load in finite populations

Kimura, Maruyama and Crow (1963) consider a locus with alleles $A$ and $A'$, genotype fitnesses $1$, $1 - hs$ and $1 - s$ for $AA$, $AA'$ and $A'A'$, forward and reverse mutation rates $u$ and $v$, and random mating in a population of effective size $N$. The load of a population with mutant frequency $x$ is

$$L(x) = 2shx(1 - x) + sx^2$$

(their equation (3)), measured relative to the fittest genotype $AA$, and the mean load is its expectation under Wright's stationary distribution of $x$ under mutation, selection and drift (their equations (2) and (4)). They evaluate this integral numerically, by confluent hypergeometric functions for genic selection, and in closed form in special cases (lethals without dominance, recessive lethals, and particular values of $4Nu$ and $4Nv$). They find that for large $Ns$ the load approaches $u$ for a recessive mutant ($h = 0$) and about $2u$ without dominance ($h = \frac12$); that in small populations the load can be considerably larger; that for a given population size a mildly deleterious mutant can cause a larger load than a more deleterious one; and that a finite population can have a smaller load than an infinite one, as for a nearly recessive mutant ($h = 0.05$, $s = 0.01$, $u = v = 10^{-5}$) near $N = 1000$, because in small populations the mutant is usually absent or fixed and is then eliminated in homozygotes, two genes per genetic death. In this model, with fitnesses $1$, $1 - hs$, $1 - s$ and forward mutation rate $u$, they state that in general the mutation load is never less than the mutation rate, except for loci where the gene frequencies are maintained by balanced selective forces; they name the underdominant case only as one where the load may exceed twice the mutation rate. The expected load is thus a ratio of two explicit integrals against the stationary density with dominance, and its dependence on $N$ is not monotone in general.

## Depends on

- [Haldane–Muller load](../../../Biology/population-genetics/mutation-selection-balance/load-mult-at-equilibrium.md)

## Expansion

1. The load function and the stationary density in the source's parametrization.
2. The expected load as a ratio of integrals, and its closed forms in the special cases listed by the source.
3. The large-$Ns$ limits $u$ and $2u$, and the small-$Ns$ approximation.
4. The nearly recessive example in which a finite population has a smaller load than an infinite one, and the explanation by elimination in homozygotes.
5. The source's statement that in general the load is never less than the mutation rate is an informal finding, not a theorem: a precise statement needs conditions on $h$, $s$, $u$, $v$ and $N$ under which the mean load is at least $u$, with the balanced-polymorphism loci excluded, and a proof.

## Sources

- M. Kimura, T. Maruyama and J. F. Crow, The mutation load in small populations, Genetics 48 (1963), 1303–1312, equations (2)–(4), discussion of Figure 2, and Summary. <https://doi.org/10.1093/genetics/48.10.1303>
