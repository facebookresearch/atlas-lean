# Variance of the stratified sample mean

A finite population is partitioned into $H \ge 1$ strata $h = 1, \dots, H$ of sizes $N_h \ge 1$, $N = \sum_h N_h$, with stratum means $\bar Y_h$ and variances $S_h^2 = \sum_{i \in h}(y_i - \bar Y_h)^2/(N_h - 1)$ ($S_h^2 = 0$ when $N_h = 1$). From each stratum draw a simple random sample without replacement of size $n_h$, $1 \le n_h \le N_h$, independently across strata. The stratified estimator $\bar y_{st} = \sum_h (N_h/N)\bar y_h$ is unbiased for the population mean and $\operatorname{Var}(\bar y_{st}) = \sum_h (N_h/N)^2(1 - n_h/N_h)S_h^2/n_h$. Choosing the $n_h$ (for example Neyman allocation $n_h \propto N_hS_h$ before rounding to integers) is a separate statement.

## Proof depends on

- [Unbiasedness of the sample mean under simple random sampling](../finite-population-survey-sampling/rand-exp-sample-mean.md): the sample mean in each stratum is unbiased under simple random sampling.
- [Variance of the sample mean under simple random sampling](../finite-population-survey-sampling/rand-exp-sq-sample-mean-sub-pop-mean.md): its variance carries the finite population correction.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Variance of a sum of independent square-integrable random variables.

## Sources

- C. L. Williams, *MthSc 406: Sampling Theory and Methods*, chapter 6 "Stratified sampling", Clemson University, <http://cecas.clemson.edu/~calvinw/MthSc406/pdf/MthSc406IntroChapter6.pdf>, standard error of the stratified mean
