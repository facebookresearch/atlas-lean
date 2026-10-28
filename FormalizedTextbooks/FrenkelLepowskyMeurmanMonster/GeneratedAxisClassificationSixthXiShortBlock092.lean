/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortNumbering
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedScalar
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiShortAddressMaskEight

/-! Original sparse masks and full signed phases certify a bounded part of actual short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Candidate sparse outputs are checked against the original full binary and phase action. -/
def generatedSixthXiShortBlock092Output : Fin 256 → GeneratedSixthXiShortAddress :=
  ![Sum.inr (Sum.inr (444, 23)),
    Sum.inr (Sum.inr (317, 21)),
    Sum.inr (Sum.inr (375, 20)),
    Sum.inr (Sum.inr (509, 22)),
    Sum.inr (Sum.inr (375, 3)),
    Sum.inr (Sum.inr (444, 0)),
    Sum.inr (Sum.inr (317, 2)),
    Sum.inr (Sum.inr (509, 1)),
    Sum.inr (Sum.inr (169, 16)),
    Sum.inr (Sum.inr (169, 17)),
    Sum.inr (Sum.inr (162, 18)),
    Sum.inr (Sum.inr (169, 19)),
    Sum.inr (Sum.inr (375, 10)),
    Sum.inr (Sum.inr (317, 9)),
    Sum.inr (Sum.inr (509, 11)),
    Sum.inr (Sum.inr (444, 8)),
    Sum.inr (Sum.inr (445, 23)),
    Sum.inr (Sum.inr (508, 22)),
    Sum.inr (Sum.inr (316, 21)),
    Sum.inr (Sum.inr (374, 20)),
    Sum.inr (Sum.inr (163, 4)),
    Sum.inr (Sum.inr (168, 5)),
    Sum.inr (Sum.inr (163, 6)),
    Sum.inr (Sum.inr (163, 7)),
    Sum.inr (Sum.inr (445, 13)),
    Sum.inr (Sum.inr (316, 14)),
    Sum.inr (Sum.inr (374, 12)),
    Sum.inr (Sum.inr (508, 15)),
    Sum.inr (Sum.inr (374, 10)),
    Sum.inr (Sum.inr (445, 8)),
    Sum.inr (Sum.inr (316, 9)),
    Sum.inr (Sum.inr (508, 11)),
    Sum.inr (Sum.inr (168, 16)),
    Sum.inr (Sum.inr (168, 17)),
    Sum.inr (Sum.inr (163, 18)),
    Sum.inr (Sum.inr (168, 19)),
    Sum.inr (Sum.inr (374, 3)),
    Sum.inr (Sum.inr (316, 2)),
    Sum.inr (Sum.inr (508, 1)),
    Sum.inr (Sum.inr (445, 0)),
    Sum.inr (Sum.inl (212, 6)),
    Sum.inr (Sum.inl (206, 3)),
    Sum.inr (Sum.inl (149, 10)),
    Sum.inr (Sum.inl (172, 15)),
    Sum.inr (Sum.inl (37, 6)),
    Sum.inr (Sum.inl (17, 0)),
    Sum.inr (Sum.inl (37, 3)),
    Sum.inr (Sum.inl (37, 15)),
    Sum.inr (Sum.inl (212, 3)),
    Sum.inr (Sum.inl (149, 15)),
    Sum.inr (Sum.inl (172, 10)),
    Sum.inr (Sum.inl (206, 6)),
    Sum.inr (Sum.inl (172, 6)),
    Sum.inr (Sum.inl (212, 15)),
    Sum.inr (Sum.inl (149, 3)),
    Sum.inr (Sum.inl (206, 10)),
    Sum.inr (Sum.inl (17, 10)),
    Sum.inr (Sum.inl (17, 9)),
    Sum.inr (Sum.inl (37, 10)),
    Sum.inr (Sum.inl (17, 3)),
    Sum.inr (Sum.inl (172, 3)),
    Sum.inr (Sum.inl (149, 6)),
    Sum.inr (Sum.inl (206, 15)),
    Sum.inr (Sum.inl (212, 10)),
    Sum.inr (Sum.inl (188, 27)),
    Sum.inr (Sum.inl (187, 46)),
    Sum.inr (Sum.inl (143, 15)),
    Sum.inr (Sum.inl (166, 18)),
    Sum.inr (Sum.inl (31, 22)),
    Sum.inr (Sum.inl (11, 5)),
    Sum.inr (Sum.inl (31, 19)),
    Sum.inr (Sum.inl (31, 31)),
    Sum.inr (Sum.inl (188, 30)),
    Sum.inr (Sum.inl (143, 10)),
    Sum.inr (Sum.inl (166, 23)),
    Sum.inr (Sum.inl (187, 43)),
    Sum.inr (Sum.inl (166, 41)),
    Sum.inr (Sum.inl (188, 32)),
    Sum.inr (Sum.inl (143, 52)),
    Sum.inr (Sum.inl (187, 21)),
    Sum.inr (Sum.inl (11, 26)),
    Sum.inr (Sum.inl (11, 42)),
    Sum.inr (Sum.inl (31, 26)),
    Sum.inr (Sum.inl (11, 53)),
    Sum.inr (Sum.inl (166, 44)),
    Sum.inr (Sum.inl (143, 49)),
    Sum.inr (Sum.inl (187, 16)),
    Sum.inr (Sum.inl (188, 37)),
    Sum.inr (Sum.inl (211, 43)),
    Sum.inr (Sum.inl (205, 54)),
    Sum.inr (Sum.inl (148, 15)),
    Sum.inr (Sum.inl (171, 6)),
    Sum.inr (Sum.inl (36, 22)),
    Sum.inr (Sum.inl (16, 5)),
    Sum.inr (Sum.inl (36, 19)),
    Sum.inr (Sum.inl (36, 31)),
    Sum.inr (Sum.inl (211, 52)),
    Sum.inr (Sum.inl (148, 16)),
    Sum.inr (Sum.inl (171, 25)),
    Sum.inr (Sum.inl (205, 41)),
    Sum.inr (Sum.inl (171, 39)),
    Sum.inr (Sum.inl (211, 10)),
    Sum.inr (Sum.inl (148, 46)),
    Sum.inr (Sum.inl (205, 23)),
    Sum.inr (Sum.inl (16, 26)),
    Sum.inr (Sum.inl (16, 42)),
    Sum.inr (Sum.inl (36, 26)),
    Sum.inr (Sum.inl (16, 53)),
    Sum.inr (Sum.inl (171, 56)),
    Sum.inr (Sum.inl (148, 49)),
    Sum.inr (Sum.inl (205, 8)),
    Sum.inr (Sum.inl (211, 21)),
    Sum.inr (Sum.inl (214, 37)),
    Sum.inr (Sum.inl (208, 52)),
    Sum.inr (Sum.inl (151, 22)),
    Sum.inr (Sum.inl (174, 2)),
    Sum.inr (Sum.inl (39, 37)),
    Sum.inr (Sum.inl (19, 5)),
    Sum.inr (Sum.inl (39, 53)),
    Sum.inr (Sum.inl (39, 10)),
    Sum.inr (Sum.inl (214, 58)),
    Sum.inr (Sum.inl (151, 9)),
    Sum.inr (Sum.inl (174, 29)),
    Sum.inr (Sum.inl (208, 43)),
    Sum.inr (Sum.inl (174, 45)),
    Sum.inr (Sum.inl (214, 10)),
    Sum.inr (Sum.inl (151, 57)),
    Sum.inr (Sum.inl (208, 27)),
    Sum.inr (Sum.inl (19, 26)),
    Sum.inr (Sum.inl (19, 42)),
    Sum.inr (Sum.inl (39, 26)),
    Sum.inr (Sum.inl (19, 53)),
    Sum.inr (Sum.inl (174, 50)),
    Sum.inr (Sum.inl (151, 38)),
    Sum.inr (Sum.inl (208, 4)),
    Sum.inr (Sum.inl (214, 21)),
    Sum.inr (Sum.inr (438, 23)),
    Sum.inr (Sum.inr (503, 22)),
    Sum.inr (Sum.inr (311, 21)),
    Sum.inr (Sum.inr (381, 20)),
    Sum.inr (Sum.inr (168, 4)),
    Sum.inr (Sum.inr (163, 5)),
    Sum.inr (Sum.inr (168, 6)),
    Sum.inr (Sum.inr (168, 7)),
    Sum.inr (Sum.inr (438, 13)),
    Sum.inr (Sum.inr (311, 14)),
    Sum.inr (Sum.inr (381, 12)),
    Sum.inr (Sum.inr (503, 15)),
    Sum.inr (Sum.inr (381, 10)),
    Sum.inr (Sum.inr (438, 8)),
    Sum.inr (Sum.inr (311, 9)),
    Sum.inr (Sum.inr (503, 11)),
    Sum.inr (Sum.inr (163, 16)),
    Sum.inr (Sum.inr (163, 17)),
    Sum.inr (Sum.inr (168, 18)),
    Sum.inr (Sum.inr (163, 19)),
    Sum.inr (Sum.inr (381, 3)),
    Sum.inr (Sum.inr (311, 2)),
    Sum.inr (Sum.inr (503, 1)),
    Sum.inr (Sum.inr (438, 0)),
    Sum.inr (Sum.inr (439, 13)),
    Sum.inr (Sum.inr (502, 15)),
    Sum.inr (Sum.inr (310, 14)),
    Sum.inr (Sum.inr (380, 12)),
    Sum.inr (Sum.inr (169, 4)),
    Sum.inr (Sum.inr (162, 5)),
    Sum.inr (Sum.inr (169, 6)),
    Sum.inr (Sum.inr (169, 7)),
    Sum.inr (Sum.inr (439, 23)),
    Sum.inr (Sum.inr (310, 21)),
    Sum.inr (Sum.inr (380, 20)),
    Sum.inr (Sum.inr (502, 22)),
    Sum.inr (Sum.inr (380, 3)),
    Sum.inr (Sum.inr (439, 0)),
    Sum.inr (Sum.inr (310, 2)),
    Sum.inr (Sum.inr (502, 1)),
    Sum.inr (Sum.inr (162, 16)),
    Sum.inr (Sum.inr (162, 17)),
    Sum.inr (Sum.inr (169, 18)),
    Sum.inr (Sum.inr (162, 19)),
    Sum.inr (Sum.inr (380, 10)),
    Sum.inr (Sum.inr (310, 9)),
    Sum.inr (Sum.inr (502, 11)),
    Sum.inr (Sum.inr (439, 8)),
    Sum.inr (Sum.inr (436, 8)),
    Sum.inr (Sum.inr (501, 11)),
    Sum.inr (Sum.inr (309, 9)),
    Sum.inr (Sum.inr (383, 10)),
    Sum.inr (Sum.inr (170, 4)),
    Sum.inr (Sum.inr (161, 5)),
    Sum.inr (Sum.inr (170, 6)),
    Sum.inr (Sum.inr (170, 7)),
    Sum.inr (Sum.inr (436, 0)),
    Sum.inr (Sum.inr (309, 2)),
    Sum.inr (Sum.inr (383, 3)),
    Sum.inr (Sum.inr (501, 1)),
    Sum.inr (Sum.inr (383, 20)),
    Sum.inr (Sum.inr (436, 23)),
    Sum.inr (Sum.inr (309, 21)),
    Sum.inr (Sum.inr (501, 22)),
    Sum.inr (Sum.inr (161, 16)),
    Sum.inr (Sum.inr (161, 17)),
    Sum.inr (Sum.inr (170, 18)),
    Sum.inr (Sum.inr (161, 19)),
    Sum.inr (Sum.inr (383, 12)),
    Sum.inr (Sum.inr (309, 14)),
    Sum.inr (Sum.inr (501, 15)),
    Sum.inr (Sum.inr (436, 13)),
    Sum.inr (Sum.inr (446, 0)),
    Sum.inr (Sum.inr (511, 1)),
    Sum.inr (Sum.inr (319, 2)),
    Sum.inr (Sum.inr (373, 3)),
    Sum.inr (Sum.inr (160, 4)),
    Sum.inr (Sum.inr (171, 5)),
    Sum.inr (Sum.inr (160, 6)),
    Sum.inr (Sum.inr (160, 7)),
    Sum.inr (Sum.inr (446, 8)),
    Sum.inr (Sum.inr (319, 9)),
    Sum.inr (Sum.inr (373, 10)),
    Sum.inr (Sum.inr (511, 11)),
    Sum.inr (Sum.inr (373, 12)),
    Sum.inr (Sum.inr (446, 13)),
    Sum.inr (Sum.inr (319, 14)),
    Sum.inr (Sum.inr (511, 15)),
    Sum.inr (Sum.inr (171, 16)),
    Sum.inr (Sum.inr (171, 17)),
    Sum.inr (Sum.inr (160, 18)),
    Sum.inr (Sum.inr (171, 19)),
    Sum.inr (Sum.inr (373, 20)),
    Sum.inr (Sum.inr (319, 21)),
    Sum.inr (Sum.inr (511, 22)),
    Sum.inr (Sum.inr (446, 23)),
    Sum.inr (Sum.inr (213, 13)),
    Sum.inr (Sum.inr (148, 1)),
    Sum.inr (Sum.inr (84, 21)),
    Sum.inr (Sum.inr (30, 10)),
    Sum.inr (Sum.inr (459, 7)),
    Sum.inr (Sum.inr (448, 5)),
    Sum.inr (Sum.inr (459, 18)),
    Sum.inr (Sum.inr (459, 4)),
    Sum.inr (Sum.inr (213, 23)),
    Sum.inr (Sum.inr (84, 14)),
    Sum.inr (Sum.inr (30, 3)),
    Sum.inr (Sum.inr (148, 11)),
    Sum.inr (Sum.inr (30, 20)),
    Sum.inr (Sum.inr (213, 0)),
    Sum.inr (Sum.inr (84, 9)),
    Sum.inr (Sum.inr (148, 15)),
    Sum.inr (Sum.inr (448, 16)),
    Sum.inr (Sum.inr (448, 17)),
    Sum.inr (Sum.inr (459, 6)),
    Sum.inr (Sum.inr (448, 19)),
    Sum.inr (Sum.inr (30, 12)),
    Sum.inr (Sum.inr (84, 2)),
    Sum.inr (Sum.inr (148, 22)),
    Sum.inr (Sum.inr (213, 8))]

/-- Exact bounded source addresses retain all preferred-sign and physical-coordinate choices. -/
def generatedSixthXiShortBlock092Input (a : Fin 256) : GeneratedSixthXiShortAddress :=
  generatedSixthXiShortNumberAddress ⟨23552 + a.val, by omega⟩

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock092InputMaskData : ℕ :=
  sixthHex% [
    "e47da0d27da0c975a0bf7da0d8bda0c6b5a0e1bda0bfbda0c0dda0eadda0",
    "d5d5a0bfdda0fceda0fee5a0fdeda0bfeda0f3fda0fbf5a0f7fda0bffda0",
    "8f05a0af05a09f0da0ff05a0c5757ff37d7fe8757f9e757ff9b57fe7bd7f",
    "c0b57f9eb57fe1dd7fcbd57ff4d57f9ed57fdded7fdfe57fdce57f9ee57f",
    "d2fd7fdafd7fd6f57f9efd7fae057f8e057fbe0d7fde057fa6757e907d7e",
    "8b757efd757e9ab57e84bd7ea3b57efdb57e82dd7ea8d57e97d57efdd57e",
    "bee57ebced7ebfed7efded7eb1fd7eb9fd7eb5f57efdfd7ecd0d7eed0d7e",
    "dd057ebd0d7e9a757dac7d7db7757dc1757da6b57db8bd7d9fb57dc1b57d",
    "bed57d94dd7dabdd7dc1dd7d82ed7d80e57d83e57dc1e57d8dfd7d85fd7d",
    "89f57dc1fd7df10d7dd10d7de1057d810d7db97d7c8f757c947d7ce27d7c",
    "85bd7c9bb57cbcbd7ce2bd7c9ddd7cb7d57c88d57ce2d57ca1ed7ca3e57c",
    "a0e57ce2e57caef57ca6f57caafd7ce2f57cd20d7cf20d7cc2057ca20d7c",
    "9c757baa7d7bb1757bc7757ba0bd7bbeb57b99bd7bc7bd7bb8dd7b92d57b",
    "add57bc7d57b84ed7b86e57b85e57bc7e57b8bfd7b83fd7b8ff57bc7fd7b",
    "f70d7bd70d7be7057b870d7bbf7d7a89757a927d7ae47d7a83b57a9dbd7a",
    "bab57ae4b57a9bd57ab1dd7a8edd7ae4dd7aa7ed7aa5e57aa6e57ae4e57a",
    "a8f57aa0f57aacfd7ae4f57ad40d7af40d7ac4057aa40d7a837d79b57579",
    "ae7d79d87d79bfb579a1bd7986b579d8b579a7dd798dd579b2d579d8d579",
    "9be57999ed799aed79d8ed7994f5799cf57990fd79d8f579e80d79c80d79",
    "f80579980d79e07d78d67578cd7d78bb7d78dcb578c2bd78e5b578bbb578",
    "c4dd78eed578d1d578bbd578f8ed78fae578f9e578bbe578f7f578fff578",
    "f3fd78bbf5788b0578ab05789b0d78fb0578887d77be7577a57d77d37d77",
    "b4b577aabd778db577d3b577acdd7786d577b9d577d3d57790ed7792e577",
    "91e577d3e5779ffd7797fd779bf577d3fd77e30d77c30d77f30577930d77",
    "ab75769d7d76867576f0757697bd7689b576aebd76f0bd768fd576a5dd76",
    "9add76f0dd76b3ed76b1e576b2e576f0e576"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock092InputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock092InputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed preferred-Q mask data, before their original equality is checked. -/
def generatedSixthXiShortBlock092OutputMaskData : ℕ :=
  sixthHex% [
    "c1eb45e6aa749a7154b9706ed7a7008de70beea700b0a700f40274c89154",
    "810345b9d06ec8327489a06edfa9549a7b45c9ef0bb0a70bf8ef0085e70b",
    "f8486efc0154abd274abdb45a07eeef67fdf8aa4ffd8e5c5b632abec72a0",
    "8f32abd132abe4d7dfa904ff91d6eed845c5d8e7df9975c5be3cfffbeeee",
    "d93aa0d132a0997aab9532a0e89dc5ecd4ffbb07dfbb0eeef5d6e4a3d7d5",
    "df0cf58d4dcfe39aa1b9daaada9aa1849aa1b17fd5fcacf5c47ee48dedcf",
    "fc0fd5bd9dcf9ad4f5df06e48c92aa849aaaccd2a1c09aaacc75cfc83cf5",
    "9fefd59fe6e4e1e6e7b7e7d6cb3cf6997dccf7aaa2adeaa9ceaaa290aaa2",
    "d40fd699dcf6a10ee7e89dcc997fd6d8edccffa4f6ba76e798a2a990aaa9",
    "d8e2a2d4aaa9d845ccdc0cf68bdfd68bd6e7b00ee6e60fd79ad4f7c895cd",
    "a642a3fc02a89f42a3c142a385e7d7c834f7f0e6e6b975cdb9d7d7f845cd",
    "df0cf79adee6c94aa8c142a8890aa38542a8f8edcdfca4f7ab77d7ab7ee6",
    "69b4413fb570436e50112f6a0eb80454f80f37b80469b8042d1d7060ce50",
    "581c41118f6a112d7050bf6a77f65032244110f00f18f80f50b0045cf80f",
    "50176a545e50038d70038441385c406e5d7112865140c76b5f500505100e",
    "6650053850057cf57131265109f44040676b31857170176b575e51128c40",
    "41180e49100e0158050d100e70bf6b74f651232571232c402c6c437a6d72",
    "06b65254f7684b600611200d7260062c60061985725456526c8443251768",
    "54f572156768322e5277fc4355280d5d200d15680619200d648f6860c652",
    "371572371c4379c4492fc578531e58015f621ec80c44880727c80c79c80c",
    "4c2d7801fe58392c4970bf62701d78318f6216c658531449008007088807",
    "40c00c4c8807406762442e5813fd7813f449850eedd30fdcafd4fcfd95c6",
    "e202a8b842a3db02a88502a8b0e7dcfd34fcc5e6ed8c75c68cd7dccd45c6",
    "ea0cfcafdeed8d0aa38502a3cd4aa8c102a3cdedc6c9a4fc9e77dc9e7eed",
    "d4e6ec82e7ddfe3cfdac7dc7b3eaa9e9aaa28aeaa9d4eaa9e10fddacdcfd",
    "940eecdd9dc7ac7fddededc7caa4fd8f76ec"
  ]

/-- Decode the complete candidate preferred-Q mask without changing its sign convention. -/
def generatedSixthXiShortBlock092OutputMask (a : Fin 256) : ℕ :=
  (generatedSixthXiShortBlock092OutputMaskData >>> (24 * a.val)) % 16777216

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock092InputNumeratorData : ℕ :=
  sixthHex% [
    "7df7df6df8e385f7e17e185f7e185f85f7e17df7df6df8e385f7e17e185f",
    "7e185f85f7e186186196175d7e185f85f7e185f7e17e185f86186196175d",
    "7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f7e185f85f7e1",
    "86186196175d7e185f85f7e185f7e17e185f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df7df6df8e385f7e17e185f7e185f85f7e186186196175d",
    "7e185f85f7e185f7e17e185f86186196175d7e185f85f7e185f7e17e185f",
    "7df7df6df8e385f7e17e185f"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock092InputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock092InputNumeratorData >>> (6 * a.val)) % 64) - 32

/-- Candidate packed signed numerators require their original equality certificate. -/
def generatedSixthXiShortBlock092OutputNumeratorData : ℕ :=
  sixthHex% [
    "7e17e16df8e37e185f8617df86186185f85f7df7df6df8e385f7e17e185f",
    "7e185f85f7e17df8616df8e38617df8618617e185f85f85f86186196175d",
    "85f7e185f7e185f7e185f7e17df8616df8e37df8618618617e185f7e17e1",
    "7e17df6e18e385f8617e17df86185f86185f85f7df95f75d7df7e17df85f",
    "7df7e17df85f7e17df6e18e37e17df7e17df86185f7df7e185f7df95f75d",
    "86185f7df85f7df7e18617e17df8616df8e37df8618618617e185f7e17e1",
    "86186196175d85f7e185f7e1"
  ]

/-- Decode each complete candidate numerator with its original sign convention. -/
def generatedSixthXiShortBlock092OutputNumerator (a : Fin 256) : ℤ :=
  Int.ofNat ((generatedSixthXiShortBlock092OutputNumeratorData >>> (6 * a.val)) % 64) - 32

set_option maxHeartbeats 96000000 in
-- Each actual preferred mask and true signed coefficient is checked against its candidate cache.
/-- Every packed field equals the complete original preferred mask or signed coefficient value. -/
theorem generatedSixth_xi_short_block092_cache (a : Fin 256) :
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock092Input a) =
      generatedSixthXiShortBlock092InputMask a ∧
    generatedSixthXiShortAddressMaskEight (generatedSixthXiShortBlock092Output a) =
      generatedSixthXiShortBlock092OutputMask a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock092Input a) =
      generatedSixthXiShortBlock092InputNumerator a ∧
    generatedSixthXiShortAddressNumerator (generatedSixthXiShortBlock092Output a) =
      generatedSixthXiShortBlock092OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Full original source phase and matrix orientation remain in every packed-row check.
/-- Packed genuine masks transport with the complete true preferred coefficient sign. -/
theorem generatedSixth_xi_short_block092_scalar (a : Fin 256) :
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14)
      (generatedSixthXiShortBlock092InputMask a) =
      generatedSixthXiShortBlock092OutputMask a ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar (generatedSixthXiShortBlock092InputMask a)) *
      generatedSixthXiShortBlock092InputNumerator a =
        generatedSixthXiShortBlock092OutputNumerator a := by
  revert a
  decide +kernel

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block092_folded_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock092Input a
    let y := generatedSixthXiShortBlock092Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFoldedScalar
      (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have hc := generatedSixth_xi_short_block092_cache a
  have hs := generatedSixth_xi_short_block092_scalar a
  simpa only [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2] using hs

set_option maxHeartbeats 96000000 in
-- Check every original binary bit, full central phase and signed coefficient numerator.
/-- All candidate outputs are the original binary images with the complete true signed values. -/
theorem generatedSixth_xi_short_block092_certificate (a : Fin 256) :
    let x := generatedSixthXiShortBlock092Input a
    let y := generatedSixthXiShortBlock092Output a
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns 14) (generatedSixthXiShortAddressMaskEight x) =
      generatedSixthXiShortAddressMaskEight y ∧
    nortonUIntegerSign (generatedSixthXiFastMaskPhase (generatedSixthXiShortAddressMaskEight x)) *
      generatedSixthXiShortAddressNumerator x = generatedSixthXiShortAddressNumerator y := by
  have h := generatedSixth_xi_short_block092_folded_certificate a
  simpa only [generatedSixth_xi_folded_scalar] using h

/-- Each checked source retains its genuine preferred sign in the actual original short action. -/
theorem generatedSixth_xi_short_block092_signed (a : Fin 256) :
    let r := generatedSixthXiShortAddressIndex (generatedSixthXiShortBlock092Input a)
    qSign (localShortPhase (generatedSixthCorrectedGenerator 4) r) *
      (griessConwayEncode generatedSixthAxis).2.1 r =
      (griessConwayEncode generatedSixthAxis).2.1
        (griessShortPermutation (generatedSixthCorrectedGenerator 4).val.2 r) :=
  generatedSixth_xi_short_address_mask_eight_signed _ _
    (generatedSixth_xi_short_block092_certificate a).1
    (generatedSixth_xi_short_block092_certificate a).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
