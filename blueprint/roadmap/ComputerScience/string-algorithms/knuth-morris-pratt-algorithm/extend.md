# Extending a KMP prefix table by one symbol

Extending a prefix table $t$ by a symbol $x$ appends the entry $(x, f)$, where $f$ is the transition of $t$ on $x$ from the state $|t|$, computed with the given Boolean equality test. When that test agrees with equality and $t$ records correct longest borders for $x_0 \dots x_{n-1}$, the extended table records correct longest borders for $x_0 \dots x_{n-1} x$; for an arbitrary test, or a table without correct borders, the appended value is only the computed fallback.
