# AEP and typical sets (finite iid)

For i.i.d. $X_1, \dots, X_n$ with law $p$ on a finite alphabet, $\varepsilon > 0$, $n \ge 1$, base-2 logarithms, and the typical
set $A_\varepsilon^{(n)}$ of strings with positive probability and $\lvert -\frac1n \log p(x^n) - H(p) \rvert \le \varepsilon$:

1. $\Pr(X^n \in A_\varepsilon^{(n)}) \to 1$ as $n \to \infty$;
2. $\lvert A_\varepsilon^{(n)} \rvert \le 2^{n(H(p) + \varepsilon)}$ for every $n$;
3. $\lvert A_\varepsilon^{(n)} \rvert \ge (1 - \varepsilon)\, 2^{n(H(p) - \varepsilon)}$ for all $n$ large enough that
   $\Pr(A_\varepsilon^{(n)}) \ge 1 - \varepsilon$.

## Depends on

- [Shannon entropy](../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

- [L² weak law of large numbers](../../Probability/laws-of-large-numbers/l2-weak-law-of-large-numbers/l2-weak-law.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019), Definition 14.2.3 and
  Properties 14.3.1 and 14.3.2, (14.13)–(14.15). <https://arxiv.org/pdf/1106.1445v8.pdf>
- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Definition 5.41 and
  Propositions 5.42 and 5.43. <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
- C. E. Shannon, A mathematical theory of communication, Bell System Technical Journal 27 (1948), Theorem 3 (the
  probability statement). <https://www.ece.uvic.ca/~agullive/shannon1948.pdf>
