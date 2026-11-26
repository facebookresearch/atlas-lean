# Survival probability of a tumour lineage in a discrete-time branching process

Model tumour growth as a discrete-time Galton–Watson process in which, at each time step, every cell independently either divides into two daughters with probability $(1+a)/2$ or dies with probability $(1-a)/2$, where $a \in (0,1)$ is the growth coefficient, the division probability minus the death probability per step. Started from a single cell, the lineage survives forever with probability

$$P_{\mathrm{surv}} = \frac{2a}{1+a} \;\approx\; 2a \quad (a \ll 1),$$

and goes extinct with probability $(1-a)/(1+a)$.

In a two-type version in which a resident cell of growth coefficient $a$ produces, upon division, one daughter carrying an additional driver mutation with probability $u$, and mutant cells have their own growth coefficient $b \ge a$, the extra driver does **not** change the survival probability of the tumour as a whole whenever $u$ is small (and, under a density limit, whenever the carrying capacity $K$ is large): the first mutant typically appears when the tumour already holds about $1/u$ cells — or about $K$ cells when $K < 1/u$ — by which time extinction is no longer possible.

## Depends on

- [Extinction probability of a Galton–Watson process](../../../Probability/branching-processes/galton-watson-process/extinction-prob.md)

## Proof depends on

- [Extinction probability is the least fixed point](../../../Probability/branching-processes/galton-watson-process/is-least-extinction-prob.md)

## Proof sketch

Let $q$ be the extinction probability of the lineage of a single cell. Conditioning on the first step, $q = \frac{1-a}{2} + \frac{1+a}{2} q^2$, whose roots are $q = 1$ and $q = (1-a)/(1+a)$; for $a > 0$ the process is supercritical, with mean offspring number $1 + a > 1$, so the extinction probability is the smaller root and $P_{\mathrm{surv}} = 1 - q = 2a/(1+a)$. Expanding for small $a$ gives the familiar $2a$, the discrete-time counterpart of Haldane's survival probability $2s$ for a slightly advantageous mutant. The claim about the additional driver is a statement about timescales rather than about the branching process itself: extinction of a supercritical lineage occurs within the first few generations with probability $q$, while the first surviving mutant lineage appears only after the resident population has grown to size of order $1/u$, so the two events are effectively decoupled and the tumour's fate is settled before the second driver matters. What the second driver does change is the *time* to a given detection size, which is where the density-limited (logistic) and exponential versions of the model differ.

## Sources

- J. G. Reiter, I. Bozic, B. Allen, K. Chatterjee, M. A. Nowak, "The effect of one additional driver mutation on tumor progression", *Evolutionary Applications* 6 (2013), 34–45, <https://doi.org/10.1111/eva.12020> (PMC3567469). Methods, "Model", and Results, first paragraphs on tumour survival probability.
- I. Bozic, T. Antal, H. Ohtsuki, et al., "Accumulation of driver and passenger mutations during tumor progression", *Proc. Natl. Acad. Sci. USA* 107 (2010), 18545–18550, <https://doi.org/10.1073/pnas.1010978107>.
