# DDH bounds give CPA bounds for ElGamal

Let $g$ generate a finite commutative group $G$ with $|G| = q$, and let an adversary with an encryption
oracle have uniform coins and make at most $n$ queries. If the DDH distinguisher built from its
oracle-simulating eavesdropper has DDH advantage at most $\varepsilon$, then the adversary's CPA
advantage against ElGamal is at most $\varepsilon$.
