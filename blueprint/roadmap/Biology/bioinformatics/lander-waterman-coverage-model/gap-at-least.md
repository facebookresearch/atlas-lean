# Last base of a gap of at least $m$ uncovered bases before coverage

Let $N$ reads of length $L$ have start positions $s_1, \dots, s_N$ on a circular genome with
positions $\{0, \dots, G-1\}$, and let $m$ be a natural number. A base $x$ is marked if no read
[covers](covers.md) any of the $m$ bases ending at $x$ (the bases $y$ with
$(x - y) \bmod G < m$), and some read covers the base after $x$ (the base $y$ with
$(y - x) \bmod G = 1$). For $m > 0$, $x$ is then the last base of a maximal uncovered run of
length at least $m$ that is followed by a covered base, and each such run is marked exactly once;
an entirely uncovered circle (for example $N = 0$) has no mark. For $m = 0$ the first condition is
empty and $x$ is marked exactly when the base after it is covered. For $G = 1$ no base has a
successor at offset $1$, so no base is marked.
