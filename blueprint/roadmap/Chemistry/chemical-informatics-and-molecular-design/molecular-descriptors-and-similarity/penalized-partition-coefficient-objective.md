# Penalized partition-coefficient objective

The standard single-objective benchmark of molecular design rewards lipophilicity and subtracts two penalties: synthetic difficulty, and the number of rings larger than six. It is computed from the molecular graph through three cheminformatic models.

For a molecule $m$, the penalized octanol–water partition objective is

$$
J(m) = \log P(m) - \mathrm{SAscore}(m) - \mathrm{RingPenalty}(m) ,
$$

where $\log P(m)$ estimates the base-ten logarithm of the octanol–water partition coefficient, $\mathrm{SAscore}(m) \in [1,10]$ is the synthetic accessibility score, larger values meaning harder synthesis, and $\mathrm{RingPenalty}(m)$ is the number of rings of $m$ containing more than six atoms, as the source's text defines it.

The ring term counts rings, not atoms: a molecule with two seven-membered rings contributes $2$, and one with a single eight-membered ring contributes $1$. Which rings are counted depends on the ring-perception convention of the implementation, typically a smallest set of smallest rings, and that convention is part of the score. The three terms are reported on different scales and summed without weights, so $J$ is an objective of convention rather than a physical quantity; it is dimensionless and is maximized. Its value depends on the implementations of $\log P$, of the accessibility score and of ring perception, which are empirical models, so values are comparable only within one fixed implementation, and the range attainable depends on the molecule set searched.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development treats $\log P$, $\mathrm{SAscore}$ and the ring-perception model as given functions on molecular graphs and defines $J$ by the display; on supplied descriptor values no graph model is needed at all. The endpoint worth recording is that a molecule with no ring larger than six, in particular an acyclic one, has zero ring penalty under any ring-perception convention that returns only cycles of the graph.

## Context

Undergraduate to graduate; a benchmark objective rather than a law of chemistry. Nigam, Pollice and Aspuru-Guzik use it as the fitness of their genetic algorithm, and it recurs across the inverse-design literature of this chapter.

## Sources

- AkshatKumar Nigam, Robert Pollice and Alán Aspuru-Guzik, *Parallel tempered genetic algorithm guided by deep neural networks for inverse molecular design*, Digital Discovery 1 (2022) 390–404, Eq. 1 and the paragraph following it, which defines the ring penalty as the number of rings larger than six. DOI [10.1039/d2dd00003b](https://doi.org/10.1039/d2dd00003b), PMC9358752.
