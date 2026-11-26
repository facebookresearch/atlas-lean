# Suffix entries of a string

For a list $s = (s_0, \dots, s_{n-1})$ over $\alpha$, let
$\hat s = (\mathrm{some}\,s_0, \dots, \mathrm{some}\,s_{n-1}, \mathrm{none})$ be its
terminated string. The suffix entries of $s$ are the list of pairs $(\hat s_{\ge i}, i)$ for
$i = 0, 1, \dots, n$ in increasing order, where $\hat s_{\ge i}$ is $\hat s$ with its first
$i$ entries removed: each nonempty suffix of $\hat s$ paired with its starting index.
