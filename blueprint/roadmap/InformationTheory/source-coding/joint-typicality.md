# Joint typicality (finite iid)

Let $(X_i, Y_i)$ be i.i.d. with law $P_{XY}$ on finite alphabets and $\varepsilon > 0$. The jointly typical set
$A_\varepsilon^{(n)}$ consists of the pairs $(x^n, y^n)$ with $\lvert -\frac1n \log P_X(x^n) - H(X) \rvert \le \varepsilon$,
$\lvert -\frac1n \log P_Y(y^n) - H(Y) \rvert \le \varepsilon$ and $\lvert -\frac1n \log P_{XY}(x^n, y^n) - H(X,Y) \rvert \le \varepsilon$
(all probabilities positive; logarithms to base 2, entropies and $I(X;Y)$ in bits). Then:

1. $\Pr[(X^n, Y^n) \in A_\varepsilon^{(n)}] \to 1$;
2. $\lvert A_\varepsilon^{(n)} \rvert \le 2^{n(H(X,Y) + \varepsilon)}$;
3. if $X'^n \sim P_X^n$ and $Y'^n \sim P_Y^n$ are independent, then
   $\Pr[(X'^n, Y'^n) \in A_\varepsilon^{(n)}] \le 2^{-n(I(X;Y) - 3\varepsilon)}$.

## Depends on

- [Shannon entropy](../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Mutual information of a finite joint law](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Proof depends on

- [AEP and typical sets (finite iid)](remaining-clauses-of-aep-and-typical-sets.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019), Section 14.5: Definition 14.5.3 and
  Properties 14.5.1, 14.5.2, (14.35), and 14.5.4, (14.39). <https://arxiv.org/pdf/1106.1445v8.pdf>
