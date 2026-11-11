/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.PartitionMembershipCore

/-! # Consumers of the quadratic membership-transducer run theorem -/

open MetaMathlibExt.Complexity.NPComplete.Partition
open MetaMathlibExt.TM2Program Cslib.Complexity.Karp
open MetaMathlibExt.BitstringEncoding Computability

example (as : List ℕ) :
    let r := as.flatMap fun a => delimit (encodeNat a)
    ∃ v S, RunLe MembershipCore.prog (r.length * (2 * r.length + 14) + 9)
      ⟨some .copy, false, Function.update (fun _ => []) .X r⟩
      ⟨some .done, v, S⟩ ∧
      S (.double .O) = encodeSS (as.map (· * 2)) as.sum :=
  MembershipCore.run as

example : ∃ v S, RunLe MembershipCore.prog 9
    ⟨some .copy, false, Function.update (fun _ => []) .X []⟩
    ⟨some .done, v, S⟩ ∧ S (.double .O) = [false] :=
  MembershipCore.run []

example : ∃ v S, RunLe MembershipCore.prog 405
    ⟨some .copy, false,
      Function.update (fun _ => []) .X (bitEncode ([0, 2, 2] : List ℕ))⟩
    ⟨some .done, v, S⟩ ∧ S (.double .O) = encodeSS [0, 4, 4] 4 :=
  MembershipCore.run [0, 2, 2]
