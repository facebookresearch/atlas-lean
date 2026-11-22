# Reducible pattern sets (Theorem 3)

For a set $P$ of patterns, let $A_n(P)$ and
$WA_n(P)$ be the sets of ascent sequences and of weak ascent sequences of length $n$ that
avoid every pattern in $P$. For each set $C$ of patterns and each pattern $\tau$ listed below,
with $B = C \cup \{\tau\}$, we have $A_n(B) = A_n(C)$ and $WA_n(B) = WA_n(C)$ for every
natural number $n$:

- $C = \{001\}$ and $\tau \in \{101, 102, 201\}$;
- $C = \{011\}$ and $\tau \in \{101, 110\}$;
- $C = \{012\}$ and $\tau \in \{102, 120\}$;
- $C = \{021\}$ and $\tau \in \{201, 210\}$;
- $C = \{000, 001\}$ and $\tau = 100$;
- $C = \{000, 011\}$ and $\tau \in \{100, 201, 210\}$;
- $C = \{000, 012\}$ and $\tau \in \{201, 210\}$;
- $C = \{000, 021\}$ and $\tau = 100$;
- $C = \{001, 010\}$ and $\tau \in \{021, 100, 110, 120, 210\}$;
- $C = \{001, 011\}$ and $\tau = 021$;
- $C = \{001, 012\}$ and $\tau = 021$;
- $C = \{001, 110\}$ and $\tau = 210$;
- $C = \{001, 120\}$ and $\tau = 210$;
- $C = \{010, 011\}$ and $\tau = 100$;
- $C = \{010, 012\}$ and $\tau \in \{101, 201\}$;
- $C = \{010, 021\}$ and $\tau \in \{100, 101, 102, 110, 120\}$;
- $C = \{001, 011, 012\}$, $\{001, 011, 100\}$ or $\{001, 012, 100\}$, and $\tau = 210$.

These are $36$ pairs $C \subsetneq B$. The paper writes $C \sim_r B$ and takes the result from
its reference [5].

## Sources

- David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Theorem 3.
