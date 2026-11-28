# Generic private agnostic learning with logarithmic dependence on the class size

For every finite class $H$ and all $\varepsilon, \alpha, \beta > 0$, the exponential mechanism with utility equal to minus the number of misclassified examples is an $\varepsilon$-differentially private agnostic learner that outputs $h$ with $\mathrm{er}_D(h) \le \min_{g \in H} \mathrm{er}_D(g) + \alpha$ with probability $1-\beta$ using

$$
n = O\!\left(\frac{\log |H| + \log(1/\beta)}{\alpha \varepsilon} + \frac{\log |H| + \log(1/\beta)}{\alpha^2}\right)
$$

examples. Hence any class learnable by a non-private algorithm with polynomial sample complexity and polynomial output length is privately learnable with polynomially many samples.

## Proof sketch

The empirical error has sensitivity $1/n$, so the exponential mechanism with parameter $\varepsilon n/2$ is $\varepsilon$-private and outputs a hypothesis whose empirical error exceeds the minimum by at most $O((\log|H| + \log(1/\beta))/(\varepsilon n))$. Uniform convergence over the finite class adds $O(\sqrt{(\log|H| + \log(1/\beta))/n})$. For a class with a polynomial-length description, apply the mechanism to the class of hypotheses describable within the output length.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [Exponential mechanism](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism.md)
- [Learners and agnostic PAC learnability](../../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Utility of the exponential mechanism](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-utility.md)
- [The exponential mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- S. P. Kasiviswanathan, H. K. Lee, K. Nissim, S. Raskhodnikova, A. Smith, "What Can We Learn Privately?", FOCS (2008); SIAM Journal on Computing 40 (2011), arXiv:0803.0924, Theorem 3.4 and Lemma 3.3.
