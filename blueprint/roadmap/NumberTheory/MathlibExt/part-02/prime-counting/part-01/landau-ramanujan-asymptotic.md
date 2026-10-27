---
article_id: af_f7e018721ddcba1d810e1887
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.landau_ramanujan_asymptotic
---

# Landau Ramanujan

Landau–Ramanujan theorem: the count of distinct naturals `m ≤ x` of the form
    `m = a ^ 2 + b ^ 2` is asymptotically equivalent to
    `c₀ * x / Real.sqrt (Real.log x)` for some constant `c₀ > 0`.

Scope note: this statement asserts only the existence of an unspecified
    positive constant `c₀`; it does not identify `c₀` with the
    Landau–Ramanujan constant (the Euler product over the primes
    `p ≡ 3 (mod 4)` in the cited result). That identification is an
    intentional omission relative to the source.

Controlling source: Labib Haddad and Charles Helou,
    "Representation of Integers by Near Quadratic Sequences,"
    Journal of Integer Sequences 15 (2012),
    `https://cs.uwaterloo.ca/journals/JIS/VOL15/Helou/helou3.tex`,
    lines 483–486. Complete-source SHA-256
    `5441e9d5677d97ca6a836146d5725a10a21bb1e60efa374e366cd803626cd1b1`;
    exact cited span (CRLF-preserving) SHA-256
    `ce727da79eee9763f20dcbafc1b04c02d719c74c58648eddb71f0e34524e91bf`.
    Proof-method source (distinct from the statement source above): the proof
    adapts Wirsing's mean-value method as presented in Gérald Tenenbaum,
    *Introduction to Analytic and Probabilistic Number Theory*, Chapter III.4.
    Concept ID: jis_dep_8a097e6d8b6de10033dfb175;
    grounded candidate: jis_grounded_b8d7333e5ca6cb47b348367c;
    corrected mentions/papers/proof-uses: 2/1/1.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists abs sum residue Class div sub log le](../part-02/weak-pntarithmetic-progression/exists-abs-sum-residue-class-div-sub-log.md)
- [Psi Residue Class](../part-02/residue-class-psi/psi-residue-class.md)
- [Tendsto psi Residue Class div self](../part-02/weak-pntarithmetic-progression/tendsto-psi-residue-class-div-self.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.LandauRamanujan](../../../../../../sources/v2/MathlibExt.md)
