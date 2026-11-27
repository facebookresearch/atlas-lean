# Reports Spec

The specified reports for a pattern list (the dictionary) and a text: a pattern $p$ is reported ending at position $i$ when $i < |\mathrm{text}|$, $p$ belongs to the dictionary, $p \ne [\,]$, and $p$ is a suffix of the specified matching state after the first $i + 1$ symbols. Only dictionary patterns are reported: with dictionary $\{ab\}$ and text $ab$, the string $b$ is a suffix of the state at $i = 1$ but is not reported.
