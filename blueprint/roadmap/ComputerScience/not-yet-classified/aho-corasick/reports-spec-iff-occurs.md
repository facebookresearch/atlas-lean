# Specified Aho-Corasick reports are exactly the occurrences

Let $p$ be a nonempty pattern in the pattern list and let $i$ be a position of the text, $i < |\text{text}|$. Then $p$ is reported ending at position $i$ (it is a suffix of the specified matching state after the first $i + 1$ symbols) if and only if the first $i + 1$ symbols of the text end with $p$.
