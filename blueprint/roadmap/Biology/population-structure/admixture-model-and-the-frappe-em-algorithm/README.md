# Admixture model and the FRAPPE EM algorithm

## The model

- [Parameters of the admixture model](params.md)
- [Reference-allele probability in the admixture model](qf.md)
- [Joint weight of an allele copy and its ancestral population](joint.md)
- [Positivity of the admixture joint weight](joint-pos.md)
- [The marginal of an allele copy](marginal-eq.md)
- [Positivity of the reference-allele probability](qf-pos.md)
- [Reference-allele probability is less than one](qf-lt-one.md)

## The data: two allele copies per genotype

- [Reference-allele indicator for a genotype copy](is-ref.md)
- [Observation of one allele copy of a genotype](copy-allele.md)
- [Polymorphic genotype data](polymorphic.md)
- [Allele-copy observations of a genotype matrix](data.md)
- [Sum over allele-copy data as a triple sum](sum-data.md)
- [Admixture log-likelihood](admixture-log-lik.md)
- [The EM log-likelihood of the allele copies is the admixture log-likelihood](log-lik-eq-admixture-log-lik.md)

## The EM theorem

- [The EM theorem for the admixture model](admixture-log-lik-le-of-em-q-le.md)
- [The admixture log-likelihood is monotone along the iterates](admixture-log-lik-iterate-monotone.md)

## The closed-form M-step

- [Ancestry responsibility of an allele copy (E-step)](resp.md)
- [Positivity of the admixture responsibilities](resp-pos.md)
- [Admixture responsibilities sum to one](sum-resp.md)
- [Expected ancestry count of an individual](anc-count.md)
- [FRAPPE update of the ancestry proportions](m-step-q.md)
- [Expected ancestry counts sum to the number of allele copies](sum-anc-count.md)
- [Positivity of the expected ancestry counts](anc-count-pos.md)
- [Positivity of the updated ancestry proportions](m-step-q-pos.md)
- [Updated ancestry proportions sum to one](m-step-q-sum.md)
- [Expected population count of a SNP](pop-count.md)
- [Expected reference-allele count of a SNP per population](ref-count.md)
- [Expected alternative-allele count of a SNP per population](alt-count.md)
- [FRAPPE update of the allele frequencies](m-step-f.md)
- [Reference and alternative counts add to the population count](ref-count-add-alt-count.md)
- [Positivity of expected reference counts on polymorphic data](ref-count-pos.md)
- [Positivity of expected alternative counts on polymorphic data](alt-count-pos.md)
- [Positivity of expected population counts on polymorphic data](pop-count-pos.md)
- [Positivity of the updated allele frequencies](m-step-f-pos.md)
- [Updated allele frequencies are less than one](m-step-f-lt-one.md)
- [The FRAPPE EM step](em-step.md)

## The M-step maximizes `Q`

- [Decomposition of the admixture EM objective](em-q-eq.md)
- [The FRAPPE update maximizes `Q(· | θ)`](em-q-le-em-step.md)
- [Each FRAPPE EM step does not decrease the admixture log-likelihood](admixture-log-lik-le-em-step.md)
- [The admixture log-likelihood is monotone along the FRAPPE EM iterates](admixture-log-lik-iterate-em-step-monoto.md)
