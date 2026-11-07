# Reducible sets of length-3 patterns for inversion sequences

An inversion sequence of
length $n$ is a sequence $e_0 e_1 \cdots e_{n-1}$ of natural numbers with $e_i \le i$ for all $i$;
write a length-3 pattern as a digit string ($101$ is the pattern $(1, 0, 1)$). For each pair
$(C, \tau)$ listed below and every $n$, every inversion sequence of length $n$ that avoids every
pattern in $C$ also avoids $\tau$, so $C \cup \{\tau\}$ and $C$ are avoided by the same inversion
sequences. The pairs are: $C = \{001\}$ with $\tau \in \{101, 102, 201\}$;
$C = \{011\}$ with $\tau \in \{101, 110\}$; $C = \{012\}$ with $\tau \in \{102, 120\}$;
$C = \{021\}$ with $\tau \in \{201, 210\}$; $C = \{000, 001\}$ with $\tau = 100$;
$C = \{000, 011\}$ with $\tau \in \{100, 201, 210\}$;
$C = \{000, 012\}$ with $\tau \in \{201, 210\}$; $C = \{000, 021\}$ with $\tau = 100$;
$C = \{001, 010\}$ with $\tau \in \{021, 100, 110, 120, 210\}$;
$C = \{001, 011\}$ with $\tau = 021$; $C = \{001, 012\}$ with $\tau = 021$;
$C = \{001, 110\}$ with $\tau = 210$; $C = \{001, 120\}$ with $\tau = 210$;
$C = \{010, 011\}$ with $\tau = 100$; $C = \{010, 012\}$ with $\tau \in \{101, 201\}$;
$C = \{010, 021\}$ with $\tau \in \{100, 101, 102, 110, 120\}$;
$C = \{001, 011, 012\}$ with $\tau = 210$; $C = \{001, 011, 100\}$ with $\tau = 210$; and
$C = \{001, 012, 100\}$ with $\tau = 210$.

## Sources

- Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24 (2024), Article A76, Theorem 2 (`integers-2024-A76-thm-2`).
