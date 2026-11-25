# ElGamal is CPA-secure if DDH is hard

Let $g$ generate a finite commutative group $G$ with $|G| = q$. An adversary with an encryption oracle,
uniform coins and at most $n$ queries has CPA advantage against ElGamal exactly equal to the DDH
advantage of the DDH distinguisher built from its oracle-simulating eavesdropper (Katz and Lindell,
Theorem 11.18, as an equality).
