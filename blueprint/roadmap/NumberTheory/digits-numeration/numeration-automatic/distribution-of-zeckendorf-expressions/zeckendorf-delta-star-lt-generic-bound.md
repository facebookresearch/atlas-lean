# Generic upper bound for $\delta^*$ (Lemma 17)

**Generic upper bound for $\delta^*$ (Lemma 17).** Let $L$ and $\tilde L$ be lists of length at
least $2$ with nonzero first entries whose periodic Zeckendorf collections satisfy
$E \subsetneq \tilde E$, and let $Q$ and $\tilde Q$ be fundamental sequences of the collections
$E^*$ and $\tilde E^*$ of $L$ and $\tilde L$. Write $\omega$ and $\tilde\omega$ for the first terms
of $Q$ and $\tilde Q$, $\gamma = \log_{\tilde\omega} \omega$, $p$ for the generic exponent of $Q$
and $\tilde Q$, $\delta^*$ for the function $\delta^*$ of $L$, $\tilde L$, $Q$, $\tilde Q$,
$\overline{\mathrm{rev}}$ for the reversal map of $L$ (Definition 23), $\varepsilon_k$ for the
$k$th entry of a coefficient function $\varepsilon$ ($k \ge 1$), and
$\sum \varepsilon Q = \sum_{k \ge 1} \varepsilon_k Q_k$ (so that $Q_1 = \omega$). Then
$\delta^*(\sum \varepsilon \tilde Q) < (\omega / \tilde\omega)^p / \gamma$ for every
$\varepsilon \in \tilde E^*$, and every $\varepsilon \in \tilde E^*$ with
$\sum \varepsilon \tilde Q \ge \tilde\omega$ satisfies
$\delta^*(\sum \varepsilon \tilde Q) <
\sum \overline{\mathrm{rev}}(\varepsilon) Q / \sum \varepsilon \tilde Q <
(\omega / \tilde\omega)^p / \gamma$.

Without $\sum \varepsilon \tilde Q \ge \tilde\omega$ (the normalization $\varepsilon_1 \ge 1$ that
the proof of Lemma 17 assumes) the middle bound fails: for $L = (1, 0)$, $\tilde L = (1, 1)$ (so
$p = 2$) and $\varepsilon = \beta^4$ (a single $1$ in the fourth entry),
$\overline{\mathrm{rev}}(\varepsilon) = \varepsilon$ and the middle quotient is
$16 \omega^4 = 2.33436\ldots$, while $(\omega / \tilde\omega)^2 / \gamma = 2.20076\ldots$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 17 (`integers-2025-A25-lem-17`).
