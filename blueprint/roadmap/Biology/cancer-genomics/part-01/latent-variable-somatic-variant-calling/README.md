# Latent-variable somatic variant calling

Calling somatic variants from paired tumour and healthy samples must combine several sources of uncertainty: whether a read is correctly mapped, whether it truly carries the variant, strand bias, and tumour impurity. A Bayesian latent-variable model over allele frequencies in healthy and cancer genome copies makes the likelihood computable in time linear in coverage, gives a unimodal likelihood for the cancer allele frequency, and turns posterior event probabilities into direct false discovery rate control.

- [Linear-time likelihood and posterior FDR control for somatic variant calls](linear-time-likelihood-and-posterior-fdr-control-for-somatic-variant-calls.md)
