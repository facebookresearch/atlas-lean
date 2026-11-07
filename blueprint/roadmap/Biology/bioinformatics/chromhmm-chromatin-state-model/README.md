# ChromHMM chromatin-state model

## The factored emission update

- [Weight of binary vectors with a mark present](ones-count.md)
- [Weight of binary vectors with a mark absent](zeros-count.md)
- [Factored per-mark update](factored-update.md)
- [Product of Bernoulli distributions sums to one](sum-bern-pmf.md)
- [Expected product-Bernoulli log-likelihood splits over marks](sum-mul-log-bern-pmf.md)
- [The factored update maximizes the expected log-likelihood](sum-mul-log-bern-pmf-le-factored-update.md)
- [Positivity of the factored update](factored-update-pos.md)
- [Factored update is below one](factored-update-lt-one.md)

## The model

- [ChromHMM parameters](params.md)
- [HMM of ChromHMM parameters](to-hmm.md)
- [Valid ChromHMM parameters](valid.md)
- [Parameter space of ChromHMM](valid-params.md)
- [Valid ChromHMM parameters give a valid HMM](to-hmm-2.md)
- [Valid HMM built from a valid ChromHMM parameter](to-valid-hmm.md)
- [ChromHMM joint weight of a state path and mark vectors](joint.md)
- [Expected number of bins in a state with a mark present](mark-ones.md)
- [Expected number of bins in a state with a mark absent](mark-zeros.md)
- [The ChromHMM M-step](m-step.md)
- [The factored update in posterior form](mark-ones-eq.md)
- [Rich data for the ChromHMM M-step](rich.md)
- [The ChromHMM update is a valid parameter](m-step-valid.md)
- [One ChromHMM step on rich data](em-step.md)
- [Positivity of the ChromHMM joint weight](joint-pos.md)
- [The ChromHMM update maximizes `Q(· | θ)`](em-q-le-em-step.md)
- [Each ChromHMM step does not decrease the log-likelihood](log-lik-le-em-step.md)
- [The log-likelihood is monotone along the ChromHMM iterates](log-lik-iterate-em-step-monotone.md)
- [EM log-likelihood as a sum of HMM log-likelihoods](log-lik-eq.md)
