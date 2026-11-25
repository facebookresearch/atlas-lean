# Correctness of a key-encapsulation mechanism

A key-encapsulation mechanism is correct when decapsulation recovers every encapsulated key: for
every $(pk, sk)$ in the support of key generation and every $(k, e)$ in the support of encapsulation
under $pk$, decapsulating $e$ with $sk$ gives $k$.
