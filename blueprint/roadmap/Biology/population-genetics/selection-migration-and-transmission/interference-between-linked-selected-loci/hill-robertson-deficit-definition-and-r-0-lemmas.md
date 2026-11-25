# Zero-recombination fixation exclusivity for alleles in repulsion

In the [finite haploid chain](two-locus-finite-wright-fisher-with-selection-an.md)
with $r=0$ and no mutation, any initially absent haplotype remains absent
almost surely for all time. In particular, if $AB$ is initially absent,

$$\mathbb P_0(A\text{ fixes and }B\text{ fixes})=0.$$

For precision distinguish two benchmark conventions.
If $P_A(r),P_B(r)$ are the **marginal fixation probabilities in this same
chain**, define
$\Delta_{\rm marg}(r)=\mathbb P_r(A\text{ and }B\text{ fix})-P_A(r)P_B(r)$.
Then $\Delta_{\rm marg}(0)=-P_A(0)P_B(0)<0$ when both marginals are positive.
If instead $a,b$ are specified fixation probabilities in **isolated
single-locus reference models**, define
$\Delta_{\rm ref}(r)=\mathbb P_r(A\text{ and }B\text{ fix})-ab$.
Then $\Delta_{\rm ref}(0)=-ab<0$ whenever $a,b>0$.
These definitions are not interchangeable for an arbitrary fitness array.

## Depends on

- [Finite two-locus haploid chain](two-locus-finite-wright-fisher-with-selection-an.md)

## Background

- [Broader Hill–Robertson scope](hill-robertson-interference.md)

## Expansion

At $r=0$, a zero count gives zero selected probability and hence zero
next-generation count almost surely. Induction and a countable
intersection give absence at every time.
Without mutation, fixation of an allele is absorbing. If both alleles
fix, then at the later of their two hitting times every individual is
$AB$, contradicting its persistent absence.
If both $Ab$ and $aB$ initially have positive counts, positive fitnesses
make both marginal fixation probabilities positive: all $M$ offspring
can copy either one of these types in the next generation, with positive
probability, immediately fixing its corresponding allele.
For a neutral $M=4$ population with counts $(0,1,1,2)$,
$P_A(0)=P_B(0)=1/4$ and $\Delta_{\rm marg}(0)=-1/16$.
Isolated neutral reference chains give the same numbers in this example.

The exclusivity result needs no assertion that either allele is favored;
it therefore also applies when an independently specified selection
model makes them beneficial. This realizes only the zero-recombination
residual named by the broader scope page. Dependence on $r>0$, the
quantitative Hill–Robertson effect and other benchmark comparisons remain
separate objectives. Population-reference probabilities must be specified,
not silently changed to same-chain marginals.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VIII.8 (Muller's ratchet and the Fisher–Muller argument: without recombination, haplotypes that are absent cannot be produced).
