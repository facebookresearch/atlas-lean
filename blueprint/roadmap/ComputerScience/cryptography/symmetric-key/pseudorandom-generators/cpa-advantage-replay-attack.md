# The stream cipher is not CPA-secure

**The stream cipher is not CPA-secure** (Katz and Lindell, Section 3.4.2: no deterministic
scheme is CPA-secure): for every generator `G` and messages `m₀ ≠ m₁`, the one-query replay
attack wins the CPA game with probability `1`, i.e. has advantage `1/2`.
