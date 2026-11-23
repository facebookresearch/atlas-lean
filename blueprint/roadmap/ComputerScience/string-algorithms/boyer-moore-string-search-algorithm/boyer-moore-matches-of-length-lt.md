# Boyer–Moore with a pattern longer than the text

Let $p$ and $t$ be words over the
alphabet $\{0, \dots, \sigma - 1\}$. If $t$ is strictly shorter than $p$, then the Boyer–Moore
matcher with pattern $p$ and text $t$ returns the empty list at cost $0$: no preprocessing or
search events are charged.
