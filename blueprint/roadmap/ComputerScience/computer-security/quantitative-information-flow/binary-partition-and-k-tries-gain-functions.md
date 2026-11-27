# Binary, partition and k-tries gain functions

For a nonempty family $\mathcal W$ of subsets of a finite set $\mathcal X$ of secrets, the *binary gain function* $g_{\mathcal W} : \mathcal W \times \mathcal X \to [0, 1]$ is
$g_{\mathcal W}(W, x) = 1$ if $x \in W$ and $0$ otherwise (see [gain functions and g-vulnerability](gain-functions-and-g-vulnerability.md)); it is positive exactly when the sets in $\mathcal W$
cover $\mathcal X$, as they do in all the cases below. Special cases:

- *2-block gain functions*, with $\mathcal W = \{W, \mathcal X \setminus W\}$ for a property $W$ of the secret;
- *partition gain functions* $g_\sim$, with $\mathcal W = \mathcal X/{\sim}$ for an equivalence relation $\sim$; the identity relation gives $g_{\mathrm{id}}$, and the universal relation gives
  the *happy* gain function with gain $1$ everywhere;
- for $k \ge 1$, the *$k$-tries gain function* $g_{\mathcal W_k}$, with $\mathcal W_k = \{W \subseteq \mathcal X \mid |W| \le k\}$, modelling an adversary allowed $k$ guesses (for $k = 0$ the
  family is $\{\emptyset\}$ and every gain is $0$, so that case is excluded).

$G_2$ and $G_\sim$ denote the sets of 2-block and of partition gain functions. A gain function is *single-optimal* if every $x$ has a guess $w$ with $g(w, x) = 1$ and
$g(w, x) = 1$, $x' \ne x$ imply $g(w, x') < 1$.

## Depends on

- [Gain functions and g-vulnerability](gain-functions-and-g-vulnerability.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section III-C, Definition 3.6 and items 1–3, and Section VI-D, Definition 6.5.
