# Selfish genetic elements: separate transmission-conflict models

Transmission biases can favor an element despite an organism-level
fitness cost, but each mechanism needs its own life cycle and result.

- **Cost-free meiotic drive:** reuse the [canonical transmission theorem](../one-locus-selection-dynamics/meiotic-drive-without-viability-differences.md).
  With equal viability, $k>1/2$ and initial frequency strictly between
  zero and one, the driving allele approaches fixation.
- **Recessive-lethal drive:** the [specified lethal model](meiotic-drive-with-a-recessive-lethal-converges.md)
  has an interior equilibrium $2k-1$ only for $1/2<k<1$.
  Complete transmission $k=1$ instead approaches a zero-viability boundary.
- **Maternal inheritance:** in the [paternal-independent reproduction model](invasion-of-a-maternally-inherited-element.md),
  strict rare invasion requires $(1-\mu)w_I>w_U$. Its initial-state,
  transmission-failure and equality cases are part of that theorem;
  the statement is not independent of every possible effect on males.
- **Biased conversion:** the [specified gene-conversion operator](gene-conversion-and-gc-biased-gene-conversion.md)
  is a transmission model distinct from mutation or ordinary viability
  selection.

## Expansion

The following original scope remains unproved rather than being credited
to the narrower transmission results.

A **drive suppressor** requires a two-locus model: specify the suppressor's
dominance, cost, sex-specific action, recombination and genotype life cycle.
For an unlinked suppressor that restores Mendelian transmission, choose
recombination fraction $1/2$ and an explicit carrier rule. A rare-suppressor
linearization can then be evaluated at the productive resident equilibrium
$2k-1$ with $1/2<k<1$. The relevant rare-genotype matrix and its invasion
criterion must actually be derived; the one-locus result does not imply
that every suppressor invades.

For **transposon copy number**, specify a probability law $z_t(k)$ on
nonnegative copy counts, a positive fitness $w(k)$ with finite nonzero
mean under that law, and a stochastic inheritance/transposition/excision
kernel $K(k,\ell)$. The chosen life cycle would update
$z_{t+1}(\ell)=\sum_k z_t(k)w(k)K(k,\ell)/\sum_k z_t(k)w(k)$.
The kernel must state whether transposition and excision rates are per
copy or per genome and how offspring inherit copies. Moment, recurrence,
persistence and equilibrium results then require their own hypotheses
and proof. The symbols $u,v$ alone do not give a universal balance of
$u-v$ against a marginal fitness cost.

Cytoplasmic incompatibility likewise needs explicit maternal/paternal
infection states and offspring-viability rules; it is not included by
calling an element maternally transmitted. This page organizes those
residual models and the linked results, not one universal conflict law.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Chapter II, Exercise 19, p. 135: the meiotic-drive model with drive in both sexes.
- T. Nagylaki, "Evolution of a large population under gene conversion", PNAS 80 (1983), 5941–5945, <https://doi.org/10.1073/pnas.80.19.5941>, abstract: the gene-conversion transmission model.
- The recessive-lethal drive and maternal-inheritance results are derived on their linked pages from the stated life cycles.
