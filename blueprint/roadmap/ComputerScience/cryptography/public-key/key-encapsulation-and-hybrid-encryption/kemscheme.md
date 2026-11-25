# Key-encapsulation mechanism

A key-encapsulation mechanism (Katz and Lindell, Section 11.3) consists of a key-generation
distribution on pairs $(pk, sk)$; an encapsulation algorithm giving, for each public key $pk$, a
distribution on pairs $(k, e)$ of a key and its encapsulation; and a deterministic decapsulation
algorithm giving, for each secret key $sk$ and encapsulation $e$, a key or $\bot$.
