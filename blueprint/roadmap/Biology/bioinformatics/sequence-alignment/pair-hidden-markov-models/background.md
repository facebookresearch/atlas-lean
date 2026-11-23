# Independence-model weight of a sequence pair

For real background frequencies $q$, a real $\eta$ and sequences $x, y$, the independence-model weight is

$$\eta^2 (1 - \eta)^{|x| + |y|} \prod_{k} q(x_k) \prod_{k} q(y_k).$$

It is the probability of $x$ and $y$ under the independence (random) model of Durbin et al. when $q$ is a probability law and $0 < \eta < 1$.

## Sources

- R. Durbin, S. R. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis: Probabilistic Models of Proteins and Nucleic Acids*, Cambridge University Press (1998).
