# Mutation as a transition on allele frequencies

Let $A$ be a finite allele set and let $Q$ be a fixed row-stochastic matrix:
$Q_{ab}\ge0$ and $\sum_bQ_{ab}=1$ for each $a$. It is the conditional
probability that a parental copy of allele $a$ becomes allele $b$.
For a probability vector $p_a\ge0$, $\sum_ap_a=1$, define

$$M_Q(p)_b=\sum_{a\in A}p_aQ_{ab}.$$

This is the distribution of the output allele of a random copy with input
law $p$. It remains in the frequency simplex and $M_I(p)=p$.
It is also the deterministic infinite-population mutation operator. For
independently mutating copies in a finite population with empirical
frequencies $p$, it gives the conditional expected new frequencies, not
an almost-sure deterministic empirical update.

For two alleles, let $u,v\in[0,1]$ be the probabilities of mutation away from
and towards the counted allele. Then

$$p'=(1-u)p+v(1-p)=\operatorname{linStep}(u+v,v,p).$$

This uses the [linear-step function](lin-step.md) algebraically; mutation
closure does not require $u+v\le1$, an extra restriction used in one
mutation-selection interpretation of that function. It is the same
[mutated-frequency operator](../diffusion-theory/wright-fisher-diffusion-with-mutation/mutated-freq.md)
with towards parameter $v$ and away parameter $u$.

With positive fixed fitnesses $w$, write $S_w$ for the
[selection map](../natural-selection-fisher-s-theorem-and-the-price/select.md).
Selection then mutation is $M_Q\circ S_w$; mutation then selection is
$S_w\circ M_Q$. They need not commute. For counted-type frequency $1/2$,
fitnesses $(2,1)$, $u=1/2$ and $v=0$, the two resulting frequencies are
$1/3$ and $2/5$. They do commute in special cases, such as $Q=I$ or
constant fitness across types.

## Depends on

- [Linear-step function](lin-step.md)
- [Two-way mutated frequency](../diffusion-theory/wright-fisher-diffusion-with-mutation/mutated-freq.md)
- [Selection map](../natural-selection-fisher-s-theorem-and-the-price/select.md)

## Background

- [Allele frequencies obtained from a random gamete](../hardy-weinberg-law/gamete.md)

## Expansion

Nonnegativity is termwise, and
$\sum_bM_Q(p)_b=\sum_ap_a\sum_bQ_{ab}=1$.
Conditioning on the parental allele proves the copy-law interpretation;
linearity of expectation proves the finite-population interpretation.
Neither creates a second canonical genotype or frequency representation.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, III.2, pp. 140–142, equation (III-1), and III.3, pp. 143–144, equation (III-10). The source's two-allele frequency recursion is stated for an infinite population; the finite-copy qualification and composition example are explicit above.
