# Life tables and direct standardization

Accounting identities of life tables for real sequences indexed by the times or ages
$0, 1, 2, \dots$ (cohort balance, death probabilities and survivorship); central death rates as
deaths over a positive exposure; and population shares, crude rates and directly standardized rates
over a finite set of categories such as age groups, with the decomposition of a difference of crude
rates into a rate effect and a composition effect.

## Cohort balance

- [Cohort size is initial size minus cumulative deaths plus net migration](cohort-balance.md)
- [Closed cohort size is initial size minus cumulative deaths](closed-cohort-balance.md)
- [Closed cohort extinct at time T: initial size equals deaths before T](extinct-cohort.md)

## Death probabilities, death rates and survivorship

- [Death probability as deaths over the number at risk](death-probability.md)
- [Central death rate as deaths over positive exposure](central-death-rate.md)
- [Deaths equal the number at risk times the death probability](mul-death-probability.md)
- [For 0 ≤ deaths ≤ number at risk, death probability is between 0 and 1](death-probability-mem-icc.md)
- [Next-age survivors are survivors times one minus the death probability](survivors-succ-eq-mul.md)
- [Survivors are the initial size times a product of survival factors](survivors-eq-mul-prod.md)
- [With 0 ≤ deaths ≤ survivors at every age, zero survivors stay zero](survivors-eq-zero-of-le.md)

## Population shares and crude rates

- [Valid population: nonnegative category sizes with a positive total](is-valid-population.md)
- [Population share of a category as its size over the total](population-share.md)
- [Population shares sum to one when the total size is nonzero](sum-population-share.md)
- [Shares of a valid population lie between 0 and 1](population-share-mem-icc.md)
- [Crude rate as the centre of mass of the rates with sizes as masses](crude-rate-eq-center-mass.md)
- [Crude rate as total events over total size](crude-rate-eq-sum-mul-div.md)
- [Crude rate as the share-weighted sum of category rates](crude-rate-eq-sum-population-share-mul.md)
- [Crude rate of central death rates is total deaths over total exposure](crude-rate-central-death-rate.md)
- [Crude rate of a valid population lies between the extreme rates](crude-rate-mem-icc.md)

## Direct standardization and rate differences

- [Directly standardized rate is the crude rate with the standard's sizes](directly-standardized-rate-eq-crude-rate.md)
- [Crude-rate difference as a rate effect plus a composition effect](crude-rate-sub-crude-rate.md)
- [With common category rates, the crude-rate gap is a composition effect](crude-rate-sub-crude-rate-of-same-rates.md)

## Related topics

- [Weighted mean](../../statistical-genetics/mendelian-randomization/weighted-mean.md): the crude rate and the directly standardized rate are weighted means of the category rates, with the sizes of the population or of the standard as weights.
