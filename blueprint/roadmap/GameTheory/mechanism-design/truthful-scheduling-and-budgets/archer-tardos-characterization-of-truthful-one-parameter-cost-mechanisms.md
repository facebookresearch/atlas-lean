# Archer–Tardos characterization of truthful one-parameter cost mechanisms

A one-parameter cost mechanism whose work curves are integrable is truthful (DSIC) if and only if its work rule is antitone and its payments have the form $P_i(c) = h_i(c_{-i}) + c_i w_i(c) + \int_{c_i}^{\infty} w_i(x, c_{-i})\, dx$. Choosing $h_i = 0$ gives an individually rational mechanism with nonnegative payments whenever $\int_0^\infty w_i(x, c_{-i})\,dx < \infty$.

## Proof sketch

This is Myerson's lemma with the sign of the private parameter reversed: monotonicity of allocation becomes antitonicity of work, and the envelope formula gives the payment.

## Depends on

- [One-parameter cost mechanism (reverse auction)](one-parameter-cost-mechanism-reverse-auction.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Myerson's lemma](../myerson-s-lemma-and-revenue-equivalence/is-incentive-compatible-on-iff.md)

## Sources

- Aaron Archer and Eva Tardos, "Truthful Mechanisms for One-Parameter Agents", Proceedings of the 42nd Annual IEEE Symposium on Foundations of Computer Science, 2001.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
