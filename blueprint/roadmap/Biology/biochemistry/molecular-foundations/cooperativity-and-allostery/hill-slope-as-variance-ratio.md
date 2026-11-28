# Hill slope as a ratio of occupancy variances

For an Adair binding curve against free ligand, the slope of the Hill plot at any saturation equals the variance of the number of bound ligands divided by $NY(1-Y)$, the variance for $N$ identical independent sites at the same saturation; it is $1$ for identical independent sites, never exceeds $N$, and equals $N$ for all-or-none binding.

**Setting.** Let $P(x)=\sum_{i=0}^N\beta_ix^i$ be an [Adair binding polynomial](adair-binding-polynomial.md) with species fractions $p_i(x)$, mean occupancy $\langle i\rangle$ and saturation $Y=\langle i\rangle/N$, where $x>0$ is the **free** ligand concentration (logarithms may be taken of $x/x^\circ$ for a reference concentration $x^\circ$; the slope is unaffected), and let $0<Y(x)<1$. The Hill plot is $\ln\big(Y/(1-Y)\big)$ against $\ln x$; its slope is

$$n_H(x)=\frac{d}{d\ln x}\,\ln\frac{Y(x)}{1-Y(x)}.$$

**Statement.**

1. The Hill slope is the variance ratio

$$n_H(x)=\frac{\operatorname{Var}(i)}{N\,Y(1-Y)},\qquad \operatorname{Var}(i)=\sum_{i=0}^N\big(i-\langle i\rangle\big)^2p_i(x).$$

2. For $N$ identical independent sites ($\beta_i=\binom Ni K^i$) the occupancy is binomial with variance $NY(1-Y)$, so $n_H\equiv1$. Independent but non-identical sites can give $n_H<1$: two sites occupied with probabilities $0.1$ and $0.9$ have $Y=1/2$, $\operatorname{Var}(i)=0.18$ and $n_H=0.36$.
3. $n_H(x)\le N$ for every $x$ with $0<Y<1$, and $n_H=N$ in the all-or-none case in which only the unliganded and fully liganded species are populated ($\beta_1=\dots=\beta_{N-1}=0$).

The Hill coefficient is conventionally the slope at half saturation, and by item 3 it is a lower bound on the number of sites $N$ for any Adair system. These statements concern equilibrium fractional occupancy against free ligand; they do not apply to fitted slopes of response curves or of curves plotted against total ligand, where even a single site can give slopes above one.

## Context

Graduate biochemistry and biophysics. The Hill coefficient is the most widely reported summary of cooperativity; the variance form shows what it measures (the breadth of the distribution of ligation states) and why a mixture of non-identical independent sites can also give $n_H<1$, which complicates diagnosing negative cooperativity. Abeliovich's further lower bound $1/N$ for negatively cooperating identical sites relies on an empirical convention (taking the observed plateau, not the true capacity, as saturation) and is not a bound under the normalization used here.

## Depends on

- [Adair binding polynomial and fractional saturation](adair-binding-polynomial.md)

## Proof depends on

- [Mean occupancy as a logarithmic derivative of the binding polynomial](mean-occupancy-as-logarithmic-derivative.md)

## Expansion

Proof: since $x\,dp_i/dx=p_i\,(i-\langle i\rangle)$, differentiating $\langle i\rangle=xP'/P$ in $\ln x$ gives $d\langle i\rangle/d\ln x=\langle i^2\rangle-\langle i\rangle^2$; then $d\ln(Y/(1-Y))/d\ln x=(dY/d\ln x)/(Y(1-Y))$ with $dY/d\ln x=\operatorname{Var}(i)/N$, which is item 1. Item 2 is the binomial variance. For item 3, $\langle i(N-i)\rangle\ge0$ gives $\langle i^2\rangle\le N\langle i\rangle$, hence $\operatorname{Var}(i)\le\langle i\rangle(N-\langle i\rangle)=N^2Y(1-Y)$, and dividing by $NY(1-Y)$ gives $n_H\le N$; when $p_i=0$ for $0<i<N$ the inequality is an equality, so $n_H=N$.

Remaining decomposition before the page can be marked ready: (i) the differentiability of $Y$ in $\ln x$ and the condition $0<Y<1$ for $x>0$ (which holds whenever some $\beta_i>0$ with $0<i\le N$) stated as a lemma; (ii) the identity $x\,dp_i/dx=p_i(i-\langle i\rangle)$ as its own lemma on the binding-polynomial page.

## Sources

- H. Abeliovich, "An empirical extremum principle for the Hill coefficient in ligand-protein interactions showing negative cooperativity", *Biophysical Journal* 89(1) (2005), 76–79, [doi.org](https://doi.org/10.1529/biophysj.105.060194); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC1366580/), introduction (the Hill coefficient as a lower limit on the number of interacting sites in positively cooperating systems; mixtures of non-identical sites also give $n_H<1$) and section "Theory", Eqs. 3–7 (Hill slope for the generalized Adair scheme, its variance form, the binomial interpretation of $N\theta(1-\theta)$, and the value $N$ in the infinite-cooperativity limit; equations rendered as images, text checked).
- M. I. Stefan and N. Le Novère, "Cooperative binding", *PLoS Computational Biology* 9(6) (2013), e1003106, [doi.org](https://doi.org/10.1371/journal.pcbi.1003106); journal HTML read at [journals.plos.org](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1003106), section "The Hill Equation" (the Hill plot and the statement that the total number of binding sites is an upper bound for $n$).
