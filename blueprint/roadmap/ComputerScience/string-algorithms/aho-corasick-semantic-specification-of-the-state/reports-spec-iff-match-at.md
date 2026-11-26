# Reports Spec iff match At

For a pattern $p$ in the dictionary with $p \ne [\,]$ and a position $i < |\mathrm{text}|$, $p$ is reported ending at position $i$ if and only if $|p| \le i + 1$ and $p$ matches the text at offset $i + 1 - |p|$ in the shared string-matching sense.
