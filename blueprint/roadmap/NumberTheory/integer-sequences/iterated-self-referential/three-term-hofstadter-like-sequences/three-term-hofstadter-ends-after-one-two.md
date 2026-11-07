# The sequence from $1, 2, 3$ dies after four terms

Run the recurrence
$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3))$ from the initial conditions
$B(1) = 1$, $B(2) = 2$, $B(3) = 3$ without padding, so that a term whose recurrence refers to a
nonpositive index, or to an index not yet computed, cannot be computed. Then the sequence has
exactly four terms: $B(4)$ can be computed and $B(5)$ cannot.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, proof of Theorem 1 (`B_3(4) = 6`).
