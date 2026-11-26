# Dispersion shrinkage for RNA-seq counts

Differential expression analysis of RNA-seq counts models each gene with a negative binomial distribution whose dispersion is the squared coefficient of variation of biological variability. With few replicates the gene-wise dispersion is poorly estimated, so empirical Bayes methods shrink it toward a prior learned across all genes; a log-normal prior matches the observed spread of dispersions across genes and avoids over-shrinking them to a common value.

- [Log-normal empirical Bayes shrinkage of negative binomial dispersion](log-normal-empirical-bayes-shrinkage-of-negative-binomial-dispersion.md)
