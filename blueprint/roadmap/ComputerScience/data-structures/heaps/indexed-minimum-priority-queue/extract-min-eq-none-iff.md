# Extraction from an indexed min queue fails exactly when it is empty

Let $q$ be an
indexed min queue over a linear order $W$ with identities in $\{0, \dots, n-1\}$. Extracting
the minimum of $q$ returns no result if and only if the heap array of $q$ has size $0$.
