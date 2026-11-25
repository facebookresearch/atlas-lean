/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PrimeCounting.RamanujanPrime

namespace MetaMathlibExt

@[expose] public section

/-- **Laishram's upper bound for Ramanujan primes.** Let $p_k$ denote the $k$-th prime, so that
$p_1 = 2$. For all natural numbers $n$ and $R$, if $R$ is the $n$-th Ramanujan prime (which
entails $n \ge 1$), then $R < p_{3n}$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL14/Noe/noe12.tex,
source file SHA-256 b63cf16b83caaaf31e14592b36ef720cdb8c29d7acb1d0c51fad733e550756c6,
THM laishram lines 152-160, exact span SHA-256
4cf034f71bb4dd02bd70f5464b47630035176520d6e76ae976119bc050561a5b,
definition lines 105-117, exact span SHA-256
aa194a945f450eec09898ade174650294052937acdca5139e43f57f9adb760c0,
task jis_grounded_1c4ec8bb1841443d9a65cadf__laishram_ramanujan_prime_bound. -/
theorem_wanted laishram_ramanujan_prime_bound (n R : ℕ)
    (hR : IsNthRamanujanPrime R n) :
    R < Nat.nth Nat.Prime (3 * n - 1)

end
end MetaMathlibExt
