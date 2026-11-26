# Counters and doubling for indexed signature schemes

(a) A secure $q$-indexed signature scheme used with a counter as its index (signing the $i$-th message at index $i$, and refusing after $q$ messages) is a secure stateful signature scheme for up to $q$ messages. (b) Two independent instances of an indexed signature scheme of capacity at least one, one used for index $0$ and the other for index $1$, form a secure indexed scheme of capacity $2$.

## Proof sketch

(a) Counter indices are distinct, so the stateful adversary is an indexed adversary. (b) The reduction guesses which instance the forgery targets, embeds its challenge there and generates the other key pair itself, losing a factor $2$.

## Depends on

- [Indexed signature scheme](indexed-signature-scheme.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
