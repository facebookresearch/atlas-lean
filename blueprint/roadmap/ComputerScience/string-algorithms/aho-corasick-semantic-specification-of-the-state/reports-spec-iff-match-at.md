# Reports Spec iff match At

For a pattern $p$ in the dictionary with $p \ne [\,]$ and a position $i < |\mathrm{text}|$, $p$ is reported ending at position $i$ if and only if $|p| \le i + 1$ and $p$ occurs in the text at offset $i + 1 - |p|$, that is, $p$ is a prefix of the text with its first $i + 1 - |p|$ symbols removed.
