/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal bounded contextual equation certificates of the independent C322 derivation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawContextPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact literal claimed equations and contextual derivations, block 000. -/
def y322TCContextRaw000 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77099], [77097, 15], .source 38614⟩,
    ⟨[77097], [], .source 38613⟩,
    ⟨[15], [77099], .contexts [
        ⟨1, true, false, [], [15]⟩,
        ⟨0, true, false, [], []⟩
      ]⟩,
    ⟨[15, 15], [], .source 7⟩,
    ⟨[], [], .contexts []⟩,
    ⟨[77099, 15], [], .contexts [
        ⟨2, true, false, [], [15]⟩,
        ⟨3, false, false, [], []⟩,
        ⟨4, false, false, [], []⟩
      ]⟩,
    ⟨[77099], [77099], .contexts []⟩,
    ⟨[77099], [77099], .contexts []⟩,
    ⟨[15], [77099], .contexts [
        ⟨2, false, false, [], []⟩,
        ⟨6, false, false, [], []⟩,
        ⟨7, false, false, [], []⟩,
        ⟨7, false, false, [], []⟩
      ]⟩,
    ⟨[1], [1], .contexts []⟩,
    ⟨[1], [1], .contexts []⟩,
    ⟨[1], [1], .contexts []⟩,
    ⟨[1], [1], .contexts [
        ⟨9, false, false, [], []⟩,
        ⟨10, false, false, [], []⟩,
        ⟨11, false, false, [], []⟩,
        ⟨11, false, false, [], []⟩
      ]⟩,
    ⟨[1, 77099], [1, 77099], .contexts []⟩,
    ⟨[1, 77099], [1, 77099], .contexts []⟩,
    ⟨[1, 15, 1, 15], [], .source 15⟩,
    ⟨[15, 1, 15, 1], [], .contexts [
        ⟨15, false, false, [0], [1]⟩
      ]⟩,
    ⟨[15, 1], [0, 14], .contexts [
        ⟨16, false, false, [], [0, 14]⟩
      ]⟩,
    ⟨[1, 1], [], .source 0⟩,
    ⟨[0], [1], .contexts [
        ⟨18, true, false, [0], []⟩
      ]⟩,
    ⟨[14], [15], .contexts [
        ⟨3, true, false, [14], []⟩
      ]⟩,
    ⟨[0, 14], [1, 15], .contexts [
        ⟨19, false, false, [], [14]⟩,
        ⟨20, false, false, [1], []⟩
      ]⟩,
    ⟨[77099], [77099], .contexts []⟩,
    ⟨[], [], .contexts []⟩,
    ⟨[], [], .contexts [
        ⟨23, false, false, [], []⟩,
        ⟨23, false, false, [], []⟩
      ]⟩,
    ⟨[1], [1], .contexts [
        ⟨24, false, false, [], [1]⟩,
        ⟨9, false, false, [], []⟩,
        ⟨10, false, false, [], []⟩
      ]⟩,
    ⟨[77099, 1], [1, 77099], .contexts [
        ⟨8, true, false, [], [1]⟩,
        ⟨17, false, false, [], []⟩,
        ⟨21, false, false, [], []⟩,
        ⟨12, false, false, [], [15]⟩,
        ⟨2, false, false, [1], []⟩,
        ⟨13, false, false, [], []⟩,
        ⟨14, false, false, [], []⟩,
        ⟨22, false, false, [1], []⟩,
        ⟨25, true, false, [], [77099]⟩
      ]⟩,
    ⟨[3], [3], .contexts []⟩,
    ⟨[3], [3], .contexts []⟩,
    ⟨[3], [3], .contexts []⟩,
    ⟨[3, 77099], [3, 77099], .contexts []⟩,
    ⟨[3, 77099], [3, 77099], .contexts []⟩,
    ⟨[3, 15, 3, 15], [], .source 23⟩,
    ⟨[15, 3, 15, 3], [], .contexts [
        ⟨32, false, false, [2], [3]⟩
      ]⟩,
    ⟨[15, 3], [2, 14], .contexts [
        ⟨33, false, false, [], [2, 14]⟩
      ]⟩,
    ⟨[3, 3], [], .source 1⟩,
    ⟨[2], [3], .contexts [
        ⟨35, true, false, [2], []⟩
      ]⟩,
    ⟨[2, 14], [3, 15], .contexts [
        ⟨36, false, false, [], [14]⟩,
        ⟨20, false, false, [3], []⟩
      ]⟩,
    ⟨[77099, 3], [77099, 3], .contexts []⟩,
    ⟨[3], [3], .contexts [
        ⟨24, false, false, [], [3]⟩,
        ⟨27, false, false, [], []⟩,
        ⟨28, false, false, [], []⟩
      ]⟩,
    ⟨[77099, 3], [3, 77099], .contexts [
        ⟨38, false, false, [], []⟩,
        ⟨8, true, false, [], [3]⟩,
        ⟨34, false, false, [], []⟩,
        ⟨37, false, false, [], []⟩,
        ⟨27, false, false, [], [15]⟩,
        ⟨28, false, false, [], [15]⟩,
        ⟨29, false, false, [], [15]⟩,
        ⟨29, false, false, [], [15]⟩,
        ⟨2, false, false, [3], []⟩,
        ⟨30, false, false, [], []⟩,
        ⟨31, false, false, [], []⟩,
        ⟨22, false, false, [3], []⟩,
        ⟨39, true, false, [], [77099]⟩
      ]⟩,
    ⟨[5], [5], .contexts []⟩,
    ⟨[5], [5], .contexts []⟩,
    ⟨[5], [5], .contexts []⟩,
    ⟨[5, 77099], [5, 77099], .contexts []⟩,
    ⟨[5, 77099], [5, 77099], .contexts []⟩,
    ⟨[5, 15, 5, 15], [], .source 31⟩,
    ⟨[15, 5, 15, 5], [], .contexts [
        ⟨46, false, false, [4], [5]⟩
      ]⟩,
    ⟨[15, 5], [4, 14], .contexts [
        ⟨47, false, false, [], [4, 14]⟩
      ]⟩,
    ⟨[5, 5], [], .source 2⟩,
    ⟨[4], [5], .contexts [
        ⟨49, true, false, [4], []⟩
      ]⟩,
    ⟨[4, 14], [5, 15], .contexts [
        ⟨50, false, false, [], [14]⟩,
        ⟨20, false, false, [5], []⟩
      ]⟩,
    ⟨[77099, 5], [77099, 5], .contexts []⟩,
    ⟨[5], [5], .contexts [
        ⟨24, false, false, [], [5]⟩,
        ⟨41, false, false, [], []⟩,
        ⟨42, false, false, [], []⟩
      ]⟩,
    ⟨[77099, 5], [5, 77099], .contexts [
        ⟨52, false, false, [], []⟩,
        ⟨8, true, false, [], [5]⟩,
        ⟨48, false, false, [], []⟩,
        ⟨51, false, false, [], []⟩,
        ⟨41, false, false, [], [15]⟩,
        ⟨42, false, false, [], [15]⟩,
        ⟨43, false, false, [], [15]⟩,
        ⟨43, false, false, [], [15]⟩,
        ⟨2, false, false, [5], []⟩,
        ⟨44, false, false, [], []⟩,
        ⟨45, false, false, [], []⟩,
        ⟨22, false, false, [5], []⟩,
        ⟨53, true, false, [], [77099]⟩
      ]⟩,
    ⟨[7], [7], .contexts []⟩,
    ⟨[7], [7], .contexts []⟩,
    ⟨[7], [7], .contexts []⟩,
    ⟨[7, 77099], [7, 77099], .contexts []⟩,
    ⟨[7, 77099], [7, 77099], .contexts []⟩,
    ⟨[7, 15, 7, 15], [], .source 39⟩,
    ⟨[15, 7], [6, 14], .contexts [
        ⟨60, false, false, [6], [14]⟩
      ]⟩,
    ⟨[7, 7], [], .source 3⟩,
    ⟨[6], [7], .contexts [
        ⟨62, true, false, [6], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 001. -/
def y322TCContextRaw001 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[6, 14], [7, 15], .contexts [
        ⟨63, false, false, [], [14]⟩,
        ⟨20, false, false, [7], []⟩
      ]⟩,
    ⟨[77099, 7], [77099, 7], .contexts []⟩,
    ⟨[7], [7], .contexts [
        ⟨24, false, false, [], [7]⟩,
        ⟨55, false, false, [], []⟩,
        ⟨56, false, false, [], []⟩
      ]⟩,
    ⟨[77099, 7], [7, 77099], .contexts [
        ⟨65, false, false, [], []⟩,
        ⟨8, true, false, [], [7]⟩,
        ⟨61, false, false, [], []⟩,
        ⟨64, false, false, [], []⟩,
        ⟨55, false, false, [], [15]⟩,
        ⟨56, false, false, [], [15]⟩,
        ⟨57, false, false, [], [15]⟩,
        ⟨57, false, false, [], [15]⟩,
        ⟨2, false, false, [7], []⟩,
        ⟨58, false, false, [], []⟩,
        ⟨59, false, false, [], []⟩,
        ⟨22, false, false, [7], []⟩,
        ⟨66, true, false, [], [77099]⟩
      ]⟩,
    ⟨[9], [9], .contexts []⟩,
    ⟨[9], [9], .contexts []⟩,
    ⟨[9], [9], .contexts []⟩,
    ⟨[9, 77099], [9, 77099], .contexts []⟩,
    ⟨[9, 77099], [9, 77099], .contexts []⟩,
    ⟨[9, 15, 9, 15], [], .source 47⟩,
    ⟨[15, 9, 15, 9], [], .contexts [
        ⟨73, false, false, [8], [9]⟩
      ]⟩,
    ⟨[15, 9], [8, 14], .contexts [
        ⟨74, false, false, [], [8, 14]⟩
      ]⟩,
    ⟨[9, 9], [], .source 4⟩,
    ⟨[8], [9], .contexts [
        ⟨76, true, false, [8], []⟩
      ]⟩,
    ⟨[8, 14], [9, 15], .contexts [
        ⟨77, false, false, [], [14]⟩,
        ⟨20, false, false, [9], []⟩
      ]⟩,
    ⟨[77099, 9], [77099, 9], .contexts []⟩,
    ⟨[9], [9], .contexts [
        ⟨24, false, false, [], [9]⟩,
        ⟨68, false, false, [], []⟩,
        ⟨69, false, false, [], []⟩
      ]⟩,
    ⟨[77099, 9], [9, 77099], .contexts [
        ⟨79, false, false, [], []⟩,
        ⟨8, true, false, [], [9]⟩,
        ⟨75, false, false, [], []⟩,
        ⟨78, false, false, [], []⟩,
        ⟨68, false, false, [], [15]⟩,
        ⟨69, false, false, [], [15]⟩,
        ⟨70, false, false, [], [15]⟩,
        ⟨70, false, false, [], [15]⟩,
        ⟨2, false, false, [9], []⟩,
        ⟨71, false, false, [], []⟩,
        ⟨72, false, false, [], []⟩,
        ⟨22, false, false, [9], []⟩,
        ⟨80, true, false, [], [77099]⟩
      ]⟩,
    ⟨[11], [11], .contexts []⟩,
    ⟨[11], [11], .contexts []⟩,
    ⟨[11], [11], .contexts []⟩,
    ⟨[11, 77099], [11, 77099], .contexts []⟩,
    ⟨[11, 77099], [11, 77099], .contexts []⟩,
    ⟨[11, 15, 11, 15], [], .source 55⟩,
    ⟨[15, 11, 15, 11], [], .contexts [
        ⟨87, false, false, [10], [11]⟩
      ]⟩,
    ⟨[15, 11], [10, 14], .contexts [
        ⟨88, false, false, [], [10, 14]⟩
      ]⟩,
    ⟨[11, 11], [], .source 5⟩,
    ⟨[10], [11], .contexts [
        ⟨90, true, false, [10], []⟩
      ]⟩,
    ⟨[10, 14], [11, 15], .contexts [
        ⟨91, false, false, [], [14]⟩,
        ⟨20, false, false, [11], []⟩
      ]⟩,
    ⟨[77099, 11], [77099, 11], .contexts []⟩,
    ⟨[11], [11], .contexts [
        ⟨24, false, false, [], [11]⟩,
        ⟨82, false, false, [], []⟩,
        ⟨83, false, false, [], []⟩
      ]⟩,
    ⟨[77099, 11], [11, 77099], .contexts [
        ⟨93, false, false, [], []⟩,
        ⟨8, true, false, [], [11]⟩,
        ⟨89, false, false, [], []⟩,
        ⟨92, false, false, [], []⟩,
        ⟨82, false, false, [], [15]⟩,
        ⟨83, false, false, [], [15]⟩,
        ⟨84, false, false, [], [15]⟩,
        ⟨84, false, false, [], [15]⟩,
        ⟨2, false, false, [11], []⟩,
        ⟨85, false, false, [], []⟩,
        ⟨86, false, false, [], []⟩,
        ⟨22, false, false, [11], []⟩,
        ⟨94, true, false, [], [77099]⟩
      ]⟩,
    ⟨[77101], [77099, 13], .source 38615⟩,
    ⟨[77099, 13], [77101], .contexts [
        ⟨96, true, false, [], []⟩
      ]⟩,
    ⟨[13, 13], [], .source 6⟩,
    ⟨[77101, 13], [77099], .contexts [
        ⟨97, true, false, [], [13]⟩,
        ⟨98, false, false, [77099], []⟩,
        ⟨7, false, false, [], []⟩
      ]⟩,
    ⟨[77101], [77101], .contexts []⟩,
    ⟨[77101], [77101], .contexts []⟩,
    ⟨[77099, 13], [77101], .contexts [
        ⟨97, false, false, [], []⟩,
        ⟨100, false, false, [], []⟩,
        ⟨101, false, false, [], []⟩,
        ⟨101, false, false, [], []⟩
      ]⟩,
    ⟨[3, 77101], [3, 77101], .contexts []⟩,
    ⟨[3, 77101], [3, 77101], .contexts []⟩,
    ⟨[3, 13, 3, 13], [], .source 22⟩,
    ⟨[13, 3, 13, 3], [], .contexts [
        ⟨105, false, false, [2], [3]⟩
      ]⟩,
    ⟨[13, 3], [2, 12], .contexts [
        ⟨106, false, false, [], [2, 12]⟩
      ]⟩,
    ⟨[12], [13], .contexts [
        ⟨98, true, false, [12], []⟩
      ]⟩,
    ⟨[2, 12], [3, 13], .contexts [
        ⟨36, false, false, [], [12]⟩,
        ⟨108, false, false, [3], []⟩
      ]⟩,
    ⟨[77101], [77101], .contexts []⟩,
    ⟨[77101, 3], [3, 77101], .contexts [
        ⟨102, true, false, [], [3]⟩,
        ⟨107, false, false, [77099], []⟩,
        ⟨109, false, false, [77099], []⟩,
        ⟨38, false, false, [], [13]⟩,
        ⟨40, false, false, [], [13]⟩,
        ⟨30, false, false, [], [13]⟩,
        ⟨31, false, false, [], [13]⟩,
        ⟨31, false, false, [], [13]⟩,
        ⟨97, false, false, [3], []⟩,
        ⟨103, false, false, [], []⟩,
        ⟨104, false, false, [], []⟩,
        ⟨110, false, false, [3], []⟩,
        ⟨39, true, false, [], [77101]⟩
      ]⟩,
    ⟨[5, 77101], [5, 77101], .contexts []⟩,
    ⟨[5, 77101], [5, 77101], .contexts []⟩,
    ⟨[5, 13, 5, 13], [], .source 30⟩,
    ⟨[13, 5, 13, 5], [], .contexts [
        ⟨114, false, false, [4], [5]⟩
      ]⟩,
    ⟨[13, 5], [4, 12], .contexts [
        ⟨115, false, false, [], [4, 12]⟩
      ]⟩,
    ⟨[4, 12], [5, 13], .contexts [
        ⟨50, false, false, [], [12]⟩,
        ⟨108, false, false, [5], []⟩
      ]⟩,
    ⟨[77101, 5], [77101, 5], .contexts []⟩,
    ⟨[77101, 5], [5, 77101], .contexts [
        ⟨118, false, false, [], []⟩,
        ⟨102, true, false, [], [5]⟩,
        ⟨116, false, false, [77099], []⟩,
        ⟨117, false, false, [77099], []⟩,
        ⟨52, false, false, [], [13]⟩,
        ⟨54, false, false, [], [13]⟩,
        ⟨44, false, false, [], [13]⟩,
        ⟨45, false, false, [], [13]⟩,
        ⟨45, false, false, [], [13]⟩,
        ⟨97, false, false, [5], []⟩,
        ⟨112, false, false, [], []⟩,
        ⟨113, false, false, [], []⟩,
        ⟨110, false, false, [5], []⟩,
        ⟨53, true, false, [], [77101]⟩
      ]⟩,
    ⟨[7, 77101], [7, 77101], .contexts []⟩,
    ⟨[7, 77101], [7, 77101], .contexts []⟩,
    ⟨[7, 13, 7, 13], [], .source 38⟩,
    ⟨[13, 7, 13, 7], [], .contexts [
        ⟨122, false, false, [6], [7]⟩
      ]⟩,
    ⟨[13, 7], [6, 12], .contexts [
        ⟨123, false, false, [], [6, 12]⟩
      ]⟩,
    ⟨[6, 12], [7, 13], .contexts [
        ⟨63, false, false, [], [12]⟩,
        ⟨108, false, false, [7], []⟩
      ]⟩,
    ⟨[77101, 7], [77101, 7], .contexts []⟩,
    ⟨[77101, 7], [7, 77101], .contexts [
        ⟨126, false, false, [], []⟩,
        ⟨102, true, false, [], [7]⟩,
        ⟨124, false, false, [77099], []⟩,
        ⟨125, false, false, [77099], []⟩,
        ⟨65, false, false, [], [13]⟩,
        ⟨67, false, false, [], [13]⟩,
        ⟨58, false, false, [], [13]⟩,
        ⟨59, false, false, [], [13]⟩,
        ⟨59, false, false, [], [13]⟩,
        ⟨97, false, false, [7], []⟩,
        ⟨120, false, false, [], []⟩,
        ⟨121, false, false, [], []⟩,
        ⟨110, false, false, [7], []⟩,
        ⟨66, true, false, [], [77101]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 002. -/
def y322TCContextRaw002 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[9, 13, 9, 13], [], .source 46⟩,
    ⟨[13, 9, 13, 9], [], .contexts [
        ⟨128, false, false, [8], [9]⟩
      ]⟩,
    ⟨[13, 9], [8, 12], .contexts [
        ⟨129, false, false, [], [8, 12]⟩
      ]⟩,
    ⟨[8, 12], [9, 13], .contexts [
        ⟨77, false, false, [], [12]⟩,
        ⟨108, false, false, [9], []⟩
      ]⟩,
    ⟨[77101, 9], [9, 77101], .contexts [
        ⟨102, true, false, [], [9]⟩,
        ⟨130, false, false, [77099], []⟩,
        ⟨131, false, false, [77099], []⟩,
        ⟨79, false, false, [], [13]⟩,
        ⟨81, false, false, [], [13]⟩,
        ⟨71, false, false, [], [13]⟩,
        ⟨72, false, false, [], [13]⟩,
        ⟨72, false, false, [], [13]⟩,
        ⟨97, false, false, [9], []⟩,
        ⟨110, false, false, [9], []⟩,
        ⟨80, true, false, [], [77101]⟩
      ]⟩,
    ⟨[11, 77101], [11, 77101], .contexts []⟩,
    ⟨[11, 77101], [11, 77101], .contexts []⟩,
    ⟨[11, 13, 11, 13], [], .source 54⟩,
    ⟨[13, 11, 13, 11], [], .contexts [
        ⟨135, false, false, [10], [11]⟩
      ]⟩,
    ⟨[13, 11], [10, 12], .contexts [
        ⟨136, false, false, [], [10, 12]⟩
      ]⟩,
    ⟨[10, 12], [11, 13], .contexts [
        ⟨91, false, false, [], [12]⟩,
        ⟨108, false, false, [11], []⟩
      ]⟩,
    ⟨[77101, 11], [77101, 11], .contexts []⟩,
    ⟨[77101, 11], [11, 77101], .contexts [
        ⟨139, false, false, [], []⟩,
        ⟨102, true, false, [], [11]⟩,
        ⟨137, false, false, [77099], []⟩,
        ⟨138, false, false, [77099], []⟩,
        ⟨93, false, false, [], [13]⟩,
        ⟨95, false, false, [], [13]⟩,
        ⟨85, false, false, [], [13]⟩,
        ⟨86, false, false, [], [13]⟩,
        ⟨86, false, false, [], [13]⟩,
        ⟨97, false, false, [11], []⟩,
        ⟨133, false, false, [], []⟩,
        ⟨134, false, false, [], []⟩,
        ⟨110, false, false, [11], []⟩,
        ⟨94, true, false, [], [77101]⟩
      ]⟩,
    ⟨[13], [13], .contexts []⟩,
    ⟨[13], [13], .contexts []⟩,
    ⟨[13], [13], .contexts []⟩,
    ⟨[13, 77101], [13, 77101], .contexts []⟩,
    ⟨[13, 77101], [13, 77101], .contexts []⟩,
    ⟨[13, 15, 13, 15, 13, 15], [], .source 63⟩,
    ⟨[13, 15, 13, 15, 13, 15], [], .contexts [
        ⟨146, false, false, [], []⟩
      ]⟩,
    ⟨[13, 15], [14, 12, 14, 12], .contexts [
        ⟨147, false, false, [], [14, 12, 14, 12]⟩
      ]⟩,
    ⟨[14, 12], [15, 13], .contexts [
        ⟨20, false, false, [], [12]⟩,
        ⟨108, false, false, [15], []⟩
      ]⟩,
    ⟨[14, 12, 14, 12], [15, 13, 15, 13], .contexts [
        ⟨149, false, false, [], [14, 12]⟩,
        ⟨20, false, false, [15, 13], [12]⟩,
        ⟨108, false, false, [15, 13, 15], []⟩
      ]⟩,
    ⟨[77101, 15], [77101, 15], .contexts []⟩,
    ⟨[77101, 15], [13, 77101], .contexts [
        ⟨151, false, false, [], []⟩,
        ⟨102, true, false, [], [15]⟩,
        ⟨148, false, false, [77099], []⟩,
        ⟨150, false, false, [77099], []⟩,
        ⟨5, false, false, [], [13, 15, 13]⟩,
        ⟨23, false, false, [], [13, 15, 13]⟩,
        ⟨4, false, false, [], [13, 15, 13]⟩,
        ⟨4, false, false, [], [13, 15, 13]⟩,
        ⟨141, false, false, [], [15, 13]⟩,
        ⟨142, false, false, [], [15, 13]⟩,
        ⟨143, false, false, [], [15, 13]⟩,
        ⟨143, false, false, [], [15, 13]⟩,
        ⟨2, false, false, [13], [13]⟩,
        ⟨97, false, false, [13], []⟩,
        ⟨144, false, false, [], []⟩,
        ⟨145, false, false, [], []⟩,
        ⟨110, false, false, [13], []⟩
      ]⟩,
    ⟨[13], [13], .contexts [
        ⟨24, false, false, [], [13]⟩,
        ⟨141, false, false, [], []⟩,
        ⟨142, false, false, [], []⟩
      ]⟩,
    ⟨[77101, 15], [13, 77101], .contexts [
        ⟨152, false, false, [], []⟩,
        ⟨153, true, false, [], [77101]⟩
      ]⟩,
    ⟨[77103], [77101, 1], .source 38616⟩,
    ⟨[77101, 1], [77103], .contexts [
        ⟨155, true, false, [], []⟩
      ]⟩,
    ⟨[77103, 1], [77101], .contexts [
        ⟨156, true, false, [], [1]⟩,
        ⟨18, false, false, [77101], []⟩,
        ⟨101, false, false, [], []⟩
      ]⟩,
    ⟨[77103], [77103], .contexts []⟩,
    ⟨[77103], [77103], .contexts []⟩,
    ⟨[77101, 1], [77103], .contexts [
        ⟨156, false, false, [], []⟩,
        ⟨158, false, false, [], []⟩,
        ⟨159, false, false, [], []⟩,
        ⟨159, false, false, [], []⟩
      ]⟩,
    ⟨[5, 77103], [5, 77103], .contexts []⟩,
    ⟨[5, 77103], [5, 77103], .contexts []⟩,
    ⟨[1, 5, 1, 5], [], .source 10⟩,
    ⟨[1, 5, 1, 5], [], .contexts [
        ⟨163, false, false, [], []⟩
      ]⟩,
    ⟨[1, 5], [4, 0], .contexts [
        ⟨164, false, false, [], [4, 0]⟩
      ]⟩,
    ⟨[4, 0], [5, 1], .contexts [
        ⟨50, false, false, [], [0]⟩,
        ⟨19, false, false, [5], []⟩
      ]⟩,
    ⟨[77103], [77103], .contexts []⟩,
    ⟨[77103, 5], [5, 77103], .contexts [
        ⟨160, true, false, [], [5]⟩,
        ⟨165, false, false, [77101], []⟩,
        ⟨166, false, false, [77101], []⟩,
        ⟨118, false, false, [], [1]⟩,
        ⟨119, false, false, [], [1]⟩,
        ⟨112, false, false, [], [1]⟩,
        ⟨113, false, false, [], [1]⟩,
        ⟨113, false, false, [], [1]⟩,
        ⟨156, false, false, [5], []⟩,
        ⟨161, false, false, [], []⟩,
        ⟨162, false, false, [], []⟩,
        ⟨167, false, false, [5], []⟩,
        ⟨53, true, false, [], [77103]⟩
      ]⟩,
    ⟨[7, 77103], [7, 77103], .contexts []⟩,
    ⟨[7, 77103], [7, 77103], .contexts []⟩,
    ⟨[1, 7, 1, 7], [], .source 11⟩,
    ⟨[1, 7, 1, 7], [], .contexts [
        ⟨171, false, false, [], []⟩
      ]⟩,
    ⟨[1, 7], [6, 0], .contexts [
        ⟨172, false, false, [], [6, 0]⟩
      ]⟩,
    ⟨[6, 0], [7, 1], .contexts [
        ⟨63, false, false, [], [0]⟩,
        ⟨19, false, false, [7], []⟩
      ]⟩,
    ⟨[77103, 7], [77103, 7], .contexts []⟩,
    ⟨[77103, 7], [7, 77103], .contexts [
        ⟨175, false, false, [], []⟩,
        ⟨160, true, false, [], [7]⟩,
        ⟨173, false, false, [77101], []⟩,
        ⟨174, false, false, [77101], []⟩,
        ⟨126, false, false, [], [1]⟩,
        ⟨127, false, false, [], [1]⟩,
        ⟨120, false, false, [], [1]⟩,
        ⟨121, false, false, [], [1]⟩,
        ⟨121, false, false, [], [1]⟩,
        ⟨156, false, false, [7], []⟩,
        ⟨169, false, false, [], []⟩,
        ⟨170, false, false, [], []⟩,
        ⟨167, false, false, [7], []⟩,
        ⟨66, true, false, [], [77103]⟩
      ]⟩,
    ⟨[11, 77103], [11, 77103], .contexts []⟩,
    ⟨[11, 77103], [11, 77103], .contexts []⟩,
    ⟨[1, 11, 1, 11], [], .source 13⟩,
    ⟨[1, 11, 1, 11], [], .contexts [
        ⟨179, false, false, [], []⟩
      ]⟩,
    ⟨[1, 11], [10, 0], .contexts [
        ⟨180, false, false, [], [10, 0]⟩
      ]⟩,
    ⟨[10, 0], [11, 1], .contexts [
        ⟨91, false, false, [], [0]⟩,
        ⟨19, false, false, [11], []⟩
      ]⟩,
    ⟨[77103, 11], [77103, 11], .contexts []⟩,
    ⟨[77103, 11], [11, 77103], .contexts [
        ⟨183, false, false, [], []⟩,
        ⟨160, true, false, [], [11]⟩,
        ⟨181, false, false, [77101], []⟩,
        ⟨182, false, false, [77101], []⟩,
        ⟨139, false, false, [], [1]⟩,
        ⟨140, false, false, [], [1]⟩,
        ⟨133, false, false, [], [1]⟩,
        ⟨134, false, false, [], [1]⟩,
        ⟨134, false, false, [], [1]⟩,
        ⟨156, false, false, [11], []⟩,
        ⟨177, false, false, [], []⟩,
        ⟨178, false, false, [], []⟩,
        ⟨167, false, false, [11], []⟩,
        ⟨94, true, false, [], [77103]⟩
      ]⟩,
    ⟨[1, 77103], [1, 77103], .contexts []⟩,
    ⟨[1, 77103], [1, 77103], .contexts []⟩,
    ⟨[1, 13, 1, 13, 1, 13], [], .source 14⟩,
    ⟨[1, 13, 1, 13, 1, 13], [], .contexts [
        ⟨187, false, false, [], []⟩
      ]⟩,
    ⟨[1, 13], [12, 0, 12, 0], .contexts [
        ⟨188, false, false, [], [12, 0, 12, 0]⟩
      ]⟩,
    ⟨[12, 0], [13, 1], .contexts [
        ⟨108, false, false, [], [0]⟩,
        ⟨19, false, false, [13], []⟩
      ]⟩,
    ⟨[12, 0, 12], [13, 1, 13], .contexts [
        ⟨190, false, false, [], [12]⟩,
        ⟨108, false, false, [13, 1], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 003. -/
def y322TCContextRaw003 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[12, 0, 12, 0], [13, 1, 13, 1], .contexts [
        ⟨191, false, false, [], [0]⟩,
        ⟨19, false, false, [13, 1, 13], []⟩
      ]⟩,
    ⟨[77103, 13], [77103, 13], .contexts []⟩,
    ⟨[77103, 13], [1, 77103], .contexts [
        ⟨193, false, false, [], []⟩,
        ⟨160, true, false, [], [13]⟩,
        ⟨189, false, false, [77101], []⟩,
        ⟨192, false, false, [77101], []⟩,
        ⟨99, false, false, [], [1, 13, 1]⟩,
        ⟨6, false, false, [], [1, 13, 1]⟩,
        ⟨7, false, false, [], [1, 13, 1]⟩,
        ⟨7, false, false, [], [1, 13, 1]⟩,
        ⟨26, false, false, [], [13, 1]⟩,
        ⟨13, false, false, [], [13, 1]⟩,
        ⟨14, false, false, [], [13, 1]⟩,
        ⟨14, false, false, [], [13, 1]⟩,
        ⟨97, false, false, [1], [1]⟩,
        ⟨156, false, false, [1], []⟩,
        ⟨185, false, false, [], []⟩,
        ⟨186, false, false, [], []⟩,
        ⟨167, false, false, [1], []⟩
      ]⟩,
    ⟨[77103, 13], [1, 77103], .contexts [
        ⟨194, false, false, [], []⟩,
        ⟨25, true, false, [], [77103]⟩
      ]⟩,
    ⟨[13, 77103], [13, 77103], .contexts []⟩,
    ⟨[13, 77103], [13, 77103], .contexts []⟩,
    ⟨[1, 15, 1, 15], [], .contexts [
        ⟨15, false, false, [], []⟩
      ]⟩,
    ⟨[1, 15], [14, 0], .contexts [
        ⟨198, false, false, [], [14, 0]⟩
      ]⟩,
    ⟨[14, 0], [15, 1], .contexts [
        ⟨20, false, false, [], [0]⟩,
        ⟨19, false, false, [15], []⟩
      ]⟩,
    ⟨[77103, 15], [77103, 15], .contexts []⟩,
    ⟨[77103, 15], [13, 77103], .contexts [
        ⟨201, false, false, [], []⟩,
        ⟨160, true, false, [], [15]⟩,
        ⟨199, false, false, [77101], []⟩,
        ⟨200, false, false, [77101], []⟩,
        ⟨151, false, false, [], [1]⟩,
        ⟨154, false, false, [], [1]⟩,
        ⟨144, false, false, [], [1]⟩,
        ⟨145, false, false, [], [1]⟩,
        ⟨145, false, false, [], [1]⟩,
        ⟨156, false, false, [13], []⟩,
        ⟨196, false, false, [], []⟩,
        ⟨197, false, false, [], []⟩,
        ⟨167, false, false, [13], []⟩,
        ⟨153, true, false, [], [77103]⟩
      ]⟩,
    ⟨[77105], [77103, 3], .source 38617⟩,
    ⟨[77103, 3], [77105], .contexts [
        ⟨203, true, false, [], []⟩
      ]⟩,
    ⟨[77105, 3], [77103], .contexts [
        ⟨204, true, false, [], [3]⟩,
        ⟨35, false, false, [77103], []⟩,
        ⟨159, false, false, [], []⟩
      ]⟩,
    ⟨[77105], [77105], .contexts []⟩,
    ⟨[77105], [77105], .contexts []⟩,
    ⟨[77103, 3], [77105], .contexts [
        ⟨204, false, false, [], []⟩,
        ⟨206, false, false, [], []⟩,
        ⟨207, false, false, [], []⟩,
        ⟨207, false, false, [], []⟩
      ]⟩,
    ⟨[3, 77105], [3, 77105], .contexts []⟩,
    ⟨[3, 77105], [3, 77105], .contexts []⟩,
    ⟨[1, 3, 1, 3, 1, 3], [], .source 9⟩,
    ⟨[3, 1, 3, 1, 3, 1], [], .contexts [
        ⟨211, false, false, [0], [1]⟩
      ]⟩,
    ⟨[3, 1], [0, 2, 0, 2], .contexts [
        ⟨212, false, false, [], [0, 2, 0, 2]⟩
      ]⟩,
    ⟨[0, 2], [1, 3], .contexts [
        ⟨19, false, false, [], [2]⟩,
        ⟨36, false, false, [1], []⟩
      ]⟩,
    ⟨[0, 2, 0], [1, 3, 1], .contexts [
        ⟨214, false, false, [], [0]⟩,
        ⟨19, false, false, [1, 3], []⟩
      ]⟩,
    ⟨[0, 2, 0, 2], [1, 3, 1, 3], .contexts [
        ⟨215, false, false, [], [2]⟩,
        ⟨36, false, false, [1, 3, 1], []⟩
      ]⟩,
    ⟨[77105, 1], [77105, 1], .contexts []⟩,
    ⟨[77105], [77105], .contexts []⟩,
    ⟨[77105, 1], [3, 77105], .contexts [
        ⟨217, false, false, [], []⟩,
        ⟨208, true, false, [], [1]⟩,
        ⟨213, false, false, [77103], []⟩,
        ⟨216, false, false, [77103], []⟩,
        ⟨157, false, false, [], [3, 1, 3]⟩,
        ⟨100, false, false, [], [3, 1, 3]⟩,
        ⟨101, false, false, [], [3, 1, 3]⟩,
        ⟨101, false, false, [], [3, 1, 3]⟩,
        ⟨111, false, false, [], [1, 3]⟩,
        ⟨103, false, false, [], [1, 3]⟩,
        ⟨104, false, false, [], [1, 3]⟩,
        ⟨104, false, false, [], [1, 3]⟩,
        ⟨156, false, false, [3], [3]⟩,
        ⟨204, false, false, [3], []⟩,
        ⟨209, false, false, [], []⟩,
        ⟨210, false, false, [], []⟩,
        ⟨218, false, false, [3], []⟩
      ]⟩,
    ⟨[77105, 1], [3, 77105], .contexts [
        ⟨219, false, false, [], []⟩,
        ⟨39, true, false, [], [77105]⟩
      ]⟩,
    ⟨[7, 77105], [7, 77105], .contexts []⟩,
    ⟨[7, 77105], [7, 77105], .contexts []⟩,
    ⟨[3, 7, 3, 7], [], .source 19⟩,
    ⟨[3, 7, 3, 7], [], .contexts [
        ⟨223, false, false, [], []⟩
      ]⟩,
    ⟨[3, 7], [6, 2], .contexts [
        ⟨224, false, false, [], [6, 2]⟩
      ]⟩,
    ⟨[6, 2], [7, 3], .contexts [
        ⟨63, false, false, [], [2]⟩,
        ⟨36, false, false, [7], []⟩
      ]⟩,
    ⟨[11, 77105], [11, 77105], .contexts []⟩,
    ⟨[11, 77105], [11, 77105], .contexts []⟩,
    ⟨[3, 11, 3, 11], [], .source 21⟩,
    ⟨[3, 11, 3, 11], [], .contexts [
        ⟨229, false, false, [], []⟩
      ]⟩,
    ⟨[3, 11], [10, 2], .contexts [
        ⟨230, false, false, [], [10, 2]⟩
      ]⟩,
    ⟨[10, 2], [11, 3], .contexts [
        ⟨91, false, false, [], [2]⟩,
        ⟨36, false, false, [11], []⟩
      ]⟩,
    ⟨[77105, 11], [77105, 11], .contexts []⟩,
    ⟨[77105, 11], [11, 77105], .contexts [
        ⟨233, false, false, [], []⟩,
        ⟨208, true, false, [], [11]⟩,
        ⟨231, false, false, [77103], []⟩,
        ⟨232, false, false, [77103], []⟩,
        ⟨183, false, false, [], [3]⟩,
        ⟨184, false, false, [], [3]⟩,
        ⟨177, false, false, [], [3]⟩,
        ⟨178, false, false, [], [3]⟩,
        ⟨178, false, false, [], [3]⟩,
        ⟨204, false, false, [11], []⟩,
        ⟨227, false, false, [], []⟩,
        ⟨228, false, false, [], []⟩,
        ⟨218, false, false, [11], []⟩,
        ⟨94, true, false, [], [77105]⟩
      ]⟩,
    ⟨[1, 77105], [1, 77105], .contexts []⟩,
    ⟨[1, 77105], [1, 77105], .contexts []⟩,
    ⟨[3, 13, 3, 13], [], .contexts [
        ⟨105, false, false, [], []⟩
      ]⟩,
    ⟨[3, 13], [12, 2], .contexts [
        ⟨237, false, false, [], [12, 2]⟩
      ]⟩,
    ⟨[12, 2], [13, 3], .contexts [
        ⟨108, false, false, [], [2]⟩,
        ⟨36, false, false, [13], []⟩
      ]⟩,
    ⟨[77105, 13], [77105, 13], .contexts []⟩,
    ⟨[77105, 13], [1, 77105], .contexts [
        ⟨240, false, false, [], []⟩,
        ⟨208, true, false, [], [13]⟩,
        ⟨238, false, false, [77103], []⟩,
        ⟨239, false, false, [77103], []⟩,
        ⟨193, false, false, [], [3]⟩,
        ⟨195, false, false, [], [3]⟩,
        ⟨185, false, false, [], [3]⟩,
        ⟨186, false, false, [], [3]⟩,
        ⟨186, false, false, [], [3]⟩,
        ⟨204, false, false, [1], []⟩,
        ⟨235, false, false, [], []⟩,
        ⟨236, false, false, [], []⟩,
        ⟨218, false, false, [1], []⟩,
        ⟨25, true, false, [], [77105]⟩
      ]⟩,
    ⟨[13, 77105], [13, 77105], .contexts []⟩,
    ⟨[13, 77105], [13, 77105], .contexts []⟩,
    ⟨[3, 15, 3, 15], [], .contexts [
        ⟨32, false, false, [], []⟩
      ]⟩,
    ⟨[3, 15], [14, 2], .contexts [
        ⟨244, false, false, [], [14, 2]⟩
      ]⟩,
    ⟨[14, 2], [15, 3], .contexts [
        ⟨20, false, false, [], [2]⟩,
        ⟨36, false, false, [15], []⟩
      ]⟩,
    ⟨[77105, 15], [77105, 15], .contexts []⟩,
    ⟨[77105, 15], [13, 77105], .contexts [
        ⟨247, false, false, [], []⟩,
        ⟨208, true, false, [], [15]⟩,
        ⟨245, false, false, [77103], []⟩,
        ⟨246, false, false, [77103], []⟩,
        ⟨201, false, false, [], [3]⟩,
        ⟨202, false, false, [], [3]⟩,
        ⟨196, false, false, [], [3]⟩,
        ⟨197, false, false, [], [3]⟩,
        ⟨197, false, false, [], [3]⟩,
        ⟨204, false, false, [13], []⟩,
        ⟨242, false, false, [], []⟩,
        ⟨243, false, false, [], []⟩,
        ⟨218, false, false, [13], []⟩,
        ⟨153, true, false, [], [77105]⟩
      ]⟩,
    ⟨[77107], [77105, 5], .source 38618⟩,
    ⟨[77105, 5], [77107], .contexts [
        ⟨249, true, false, [], []⟩
      ]⟩,
    ⟨[77107, 5], [77105], .contexts [
        ⟨250, true, false, [], [5]⟩,
        ⟨49, false, false, [77105], []⟩,
        ⟨207, false, false, [], []⟩
      ]⟩,
    ⟨[77107], [77107], .contexts []⟩,
    ⟨[77107], [77107], .contexts []⟩,
    ⟨[77105, 5], [77107], .contexts [
        ⟨250, false, false, [], []⟩,
        ⟨252, false, false, [], []⟩,
        ⟨253, false, false, [], []⟩,
        ⟨253, false, false, [], []⟩
      ]⟩,
    ⟨[5, 1, 5, 1], [], .contexts [
        ⟨163, false, false, [0], [1]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 004. -/
def y322TCContextRaw004 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[5, 1], [0, 4], .contexts [
        ⟨255, false, false, [], [0, 4]⟩
      ]⟩,
    ⟨[0, 4], [1, 5], .contexts [
        ⟨19, false, false, [], [4]⟩,
        ⟨50, false, false, [1], []⟩
      ]⟩,
    ⟨[77107], [77107], .contexts []⟩,
    ⟨[77107, 1], [3, 77107], .contexts [
        ⟨254, true, false, [], [1]⟩,
        ⟨256, false, false, [77105], []⟩,
        ⟨257, false, false, [77105], []⟩,
        ⟨217, false, false, [], [5]⟩,
        ⟨220, false, false, [], [5]⟩,
        ⟨209, false, false, [], [5]⟩,
        ⟨210, false, false, [], [5]⟩,
        ⟨210, false, false, [], [5]⟩,
        ⟨250, false, false, [3], []⟩,
        ⟨258, false, false, [3], []⟩,
        ⟨39, true, false, [], [77107]⟩
      ]⟩,
    ⟨[5, 77107], [5, 77107], .contexts []⟩,
    ⟨[5, 77107], [5, 77107], .contexts []⟩,
    ⟨[3, 5, 3, 5, 3, 5], [], .source 18⟩,
    ⟨[5, 3, 5, 3, 5, 3], [], .contexts [
        ⟨262, false, false, [2], [3]⟩
      ]⟩,
    ⟨[5, 3], [2, 4, 2, 4], .contexts [
        ⟨263, false, false, [], [2, 4, 2, 4]⟩
      ]⟩,
    ⟨[2, 4], [3, 5], .contexts [
        ⟨36, false, false, [], [4]⟩,
        ⟨50, false, false, [3], []⟩
      ]⟩,
    ⟨[2, 4, 2], [3, 5, 3], .contexts [
        ⟨265, false, false, [], [2]⟩,
        ⟨36, false, false, [3, 5], []⟩
      ]⟩,
    ⟨[2, 4, 2, 4], [3, 5, 3, 5], .contexts [
        ⟨266, false, false, [], [4]⟩,
        ⟨50, false, false, [3, 5, 3], []⟩
      ]⟩,
    ⟨[77107, 3], [77107, 3], .contexts []⟩,
    ⟨[77107, 3], [5, 77107], .contexts [
        ⟨268, false, false, [], []⟩,
        ⟨254, true, false, [], [3]⟩,
        ⟨264, false, false, [77105], []⟩,
        ⟨267, false, false, [77105], []⟩,
        ⟨205, false, false, [], [5, 3, 5]⟩,
        ⟨158, false, false, [], [5, 3, 5]⟩,
        ⟨159, false, false, [], [5, 3, 5]⟩,
        ⟨159, false, false, [], [5, 3, 5]⟩,
        ⟨168, false, false, [], [3, 5]⟩,
        ⟨161, false, false, [], [3, 5]⟩,
        ⟨162, false, false, [], [3, 5]⟩,
        ⟨162, false, false, [], [3, 5]⟩,
        ⟨204, false, false, [5], [5]⟩,
        ⟨250, false, false, [5], []⟩,
        ⟨260, false, false, [], []⟩,
        ⟨261, false, false, [], []⟩,
        ⟨258, false, false, [5], []⟩
      ]⟩,
    ⟨[77107, 3], [5, 77107], .contexts [
        ⟨269, false, false, [], []⟩,
        ⟨53, true, false, [], [77107]⟩
      ]⟩,
    ⟨[11, 77107], [11, 77107], .contexts []⟩,
    ⟨[11, 77107], [11, 77107], .contexts []⟩,
    ⟨[5, 11, 5, 11], [], .source 29⟩,
    ⟨[5, 11, 5, 11], [], .contexts [
        ⟨273, false, false, [], []⟩
      ]⟩,
    ⟨[5, 11], [10, 4], .contexts [
        ⟨274, false, false, [], [10, 4]⟩
      ]⟩,
    ⟨[10, 4], [11, 5], .contexts [
        ⟨91, false, false, [], [4]⟩,
        ⟨50, false, false, [11], []⟩
      ]⟩,
    ⟨[77107, 11], [77107, 11], .contexts []⟩,
    ⟨[77107, 11], [11, 77107], .contexts [
        ⟨277, false, false, [], []⟩,
        ⟨254, true, false, [], [11]⟩,
        ⟨275, false, false, [77105], []⟩,
        ⟨276, false, false, [77105], []⟩,
        ⟨233, false, false, [], [5]⟩,
        ⟨234, false, false, [], [5]⟩,
        ⟨227, false, false, [], [5]⟩,
        ⟨228, false, false, [], [5]⟩,
        ⟨228, false, false, [], [5]⟩,
        ⟨250, false, false, [11], []⟩,
        ⟨271, false, false, [], []⟩,
        ⟨272, false, false, [], []⟩,
        ⟨258, false, false, [11], []⟩,
        ⟨94, true, false, [], [77107]⟩
      ]⟩,
    ⟨[1, 77107], [1, 77107], .contexts []⟩,
    ⟨[1, 77107], [1, 77107], .contexts []⟩,
    ⟨[1, 77107], [1, 77107], .contexts []⟩,
    ⟨[5, 13, 5, 13], [], .contexts [
        ⟨114, false, false, [], []⟩
      ]⟩,
    ⟨[5, 13], [12, 4], .contexts [
        ⟨282, false, false, [], [12, 4]⟩
      ]⟩,
    ⟨[12, 4], [13, 5], .contexts [
        ⟨108, false, false, [], [4]⟩,
        ⟨50, false, false, [13], []⟩
      ]⟩,
    ⟨[77107, 13], [77107, 13], .contexts []⟩,
    ⟨[77107, 13], [1, 77107], .contexts [
        ⟨285, false, false, [], []⟩,
        ⟨254, true, false, [], [13]⟩,
        ⟨283, false, false, [77105], []⟩,
        ⟨284, false, false, [77105], []⟩,
        ⟨240, false, false, [], [5]⟩,
        ⟨241, false, false, [], [5]⟩,
        ⟨235, false, false, [], [5]⟩,
        ⟨236, false, false, [], [5]⟩,
        ⟨236, false, false, [], [5]⟩,
        ⟨250, false, false, [1], []⟩,
        ⟨279, false, false, [], []⟩,
        ⟨280, false, false, [], []⟩,
        ⟨281, false, false, [], []⟩,
        ⟨258, false, false, [1], []⟩,
        ⟨25, true, false, [], [77107]⟩
      ]⟩,
    ⟨[13, 77107], [13, 77107], .contexts []⟩,
    ⟨[13, 77107], [13, 77107], .contexts []⟩,
    ⟨[5, 15, 5, 15], [], .contexts [
        ⟨46, false, false, [], []⟩
      ]⟩,
    ⟨[5, 15], [14, 4], .contexts [
        ⟨289, false, false, [], [14, 4]⟩
      ]⟩,
    ⟨[14, 4], [15, 5], .contexts [
        ⟨20, false, false, [], [4]⟩,
        ⟨50, false, false, [15], []⟩
      ]⟩,
    ⟨[77107, 15], [77107, 15], .contexts []⟩,
    ⟨[77107, 15], [13, 77107], .contexts [
        ⟨292, false, false, [], []⟩,
        ⟨254, true, false, [], [15]⟩,
        ⟨290, false, false, [77105], []⟩,
        ⟨291, false, false, [77105], []⟩,
        ⟨247, false, false, [], [5]⟩,
        ⟨248, false, false, [], [5]⟩,
        ⟨242, false, false, [], [5]⟩,
        ⟨243, false, false, [], [5]⟩,
        ⟨243, false, false, [], [5]⟩,
        ⟨250, false, false, [13], []⟩,
        ⟨287, false, false, [], []⟩,
        ⟨288, false, false, [], []⟩,
        ⟨258, false, false, [13], []⟩,
        ⟨153, true, false, [], [77107]⟩
      ]⟩,
    ⟨[77109], [77107, 9], .source 38619⟩,
    ⟨[77107, 9], [77109], .contexts [
        ⟨294, true, false, [], []⟩
      ]⟩,
    ⟨[77109, 9], [77107], .contexts [
        ⟨295, true, false, [], [9]⟩,
        ⟨76, false, false, [77107], []⟩,
        ⟨253, false, false, [], []⟩
      ]⟩,
    ⟨[77107, 9], [77109], .contexts [
        ⟨295, false, false, [], []⟩
      ]⟩,
    ⟨[77109], [77109], .contexts []⟩,
    ⟨[77109], [77109], .contexts []⟩,
    ⟨[77107, 9], [77109], .contexts [
        ⟨297, false, false, [], []⟩,
        ⟨298, false, false, [], []⟩,
        ⟨299, false, false, [], []⟩,
        ⟨299, false, false, [], []⟩
      ]⟩,
    ⟨[77107, 3], [5, 77107], .contexts [
        ⟨268, false, false, [], []⟩,
        ⟨270, false, false, [], []⟩,
        ⟨260, false, false, [], []⟩,
        ⟨261, false, false, [], []⟩,
        ⟨261, false, false, [], []⟩
      ]⟩,
    ⟨[5, 77109], [5, 77109], .contexts []⟩,
    ⟨[5, 77109], [5, 77109], .contexts []⟩,
    ⟨[3, 9, 3, 9], [], .source 20⟩,
    ⟨[9, 3, 9, 3], [], .contexts [
        ⟨304, false, false, [2], [3]⟩
      ]⟩,
    ⟨[9, 3], [2, 8], .contexts [
        ⟨305, false, false, [], [2, 8]⟩
      ]⟩,
    ⟨[2, 8], [3, 9], .contexts [
        ⟨36, false, false, [], [8]⟩,
        ⟨77, false, false, [3], []⟩
      ]⟩,
    ⟨[77109, 3], [77109, 3], .contexts []⟩,
    ⟨[77109], [77109], .contexts []⟩,
    ⟨[77107, 13], [1, 77107], .contexts [
        ⟨285, false, false, [], []⟩,
        ⟨286, false, false, [], []⟩,
        ⟨279, false, false, [], []⟩,
        ⟨281, false, false, [], []⟩,
        ⟨281, false, false, [], []⟩
      ]⟩,
    ⟨[1, 77109], [1, 77109], .contexts []⟩,
    ⟨[1, 77109], [1, 77109], .contexts []⟩,
    ⟨[1, 77109], [1, 77109], .contexts []⟩,
    ⟨[9, 13, 9, 13], [], .contexts [
        ⟨128, false, false, [], []⟩
      ]⟩,
    ⟨[9, 13], [12, 8], .contexts [
        ⟨314, false, false, [], [12, 8]⟩
      ]⟩,
    ⟨[12, 8], [13, 9], .contexts [
        ⟨108, false, false, [], [8]⟩,
        ⟨77, false, false, [13], []⟩
      ]⟩,
    ⟨[77109, 13], [77109, 13], .contexts []⟩,
    ⟨[77109, 13], [1, 77109], .contexts [
        ⟨317, false, false, [], []⟩,
        ⟨300, true, false, [], [13]⟩,
        ⟨315, false, false, [77107], []⟩,
        ⟨316, false, false, [77107], []⟩,
        ⟨310, false, false, [], [9]⟩,
        ⟨295, false, false, [1], []⟩,
        ⟨311, false, false, [], []⟩,
        ⟨312, false, false, [], []⟩,
        ⟨313, false, false, [], []⟩,
        ⟨309, false, false, [1], []⟩,
        ⟨25, true, false, [], [77109]⟩
      ]⟩,
    ⟨[77107, 15], [13, 77107], .contexts [
        ⟨292, false, false, [], []⟩,
        ⟨293, false, false, [], []⟩,
        ⟨287, false, false, [], []⟩,
        ⟨288, false, false, [], []⟩,
        ⟨288, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 005. -/
def y322TCContextRaw005 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[13, 77109], [13, 77109], .contexts []⟩,
    ⟨[13, 77109], [13, 77109], .contexts []⟩,
    ⟨[9, 15, 9, 15], [], .contexts [
        ⟨73, false, false, [], []⟩
      ]⟩,
    ⟨[9, 15], [14, 8], .contexts [
        ⟨322, false, false, [], [14, 8]⟩
      ]⟩,
    ⟨[14, 8], [15, 9], .contexts [
        ⟨20, false, false, [], [8]⟩,
        ⟨77, false, false, [15], []⟩
      ]⟩,
    ⟨[77109, 15], [77109, 15], .contexts []⟩,
    ⟨[77109, 15], [13, 77109], .contexts [
        ⟨325, false, false, [], []⟩,
        ⟨300, true, false, [], [15]⟩,
        ⟨323, false, false, [77107], []⟩,
        ⟨324, false, false, [77107], []⟩,
        ⟨319, false, false, [], [9]⟩,
        ⟨295, false, false, [13], []⟩,
        ⟨320, false, false, [], []⟩,
        ⟨321, false, false, [], []⟩,
        ⟨309, false, false, [13], []⟩,
        ⟨153, true, false, [], [77109]⟩
      ]⟩,
    ⟨[77111], [77109, 11], .source 38620⟩,
    ⟨[77109, 11], [77111], .contexts [
        ⟨327, true, false, [], []⟩
      ]⟩,
    ⟨[77109, 11], [77111], .contexts [
        ⟨328, false, false, [], []⟩
      ]⟩,
    ⟨[77111], [77111], .contexts []⟩,
    ⟨[77111], [77111], .contexts []⟩,
    ⟨[77109, 11], [77111], .contexts [
        ⟨329, false, false, [], []⟩,
        ⟨330, false, false, [], []⟩,
        ⟨331, false, false, [], []⟩,
        ⟨331, false, false, [], []⟩
      ]⟩,
    ⟨[77109, 3], [5, 77109], .contexts [
        ⟨308, false, false, [], []⟩,
        ⟨308, false, false, [], []⟩,
        ⟨300, true, false, [], [3]⟩,
        ⟨306, false, false, [77107], []⟩,
        ⟨307, false, false, [77107], []⟩,
        ⟨301, false, false, [], [9]⟩,
        ⟨295, false, false, [5], []⟩,
        ⟨302, false, false, [], []⟩,
        ⟨303, false, false, [], []⟩,
        ⟨309, false, false, [5], []⟩,
        ⟨53, true, false, [], [77109]⟩,
        ⟨302, false, false, [], []⟩,
        ⟨303, false, false, [], []⟩,
        ⟨303, false, false, [], []⟩
      ]⟩,
    ⟨[11, 3, 11, 3], [], .contexts [
        ⟨229, false, false, [2], [3]⟩
      ]⟩,
    ⟨[11, 3], [2, 10], .contexts [
        ⟨334, false, false, [], [2, 10]⟩
      ]⟩,
    ⟨[2, 10], [3, 11], .contexts [
        ⟨36, false, false, [], [10]⟩,
        ⟨91, false, false, [3], []⟩
      ]⟩,
    ⟨[77111], [77111], .contexts []⟩,
    ⟨[77107, 11], [11, 77107], .contexts [
        ⟨278, false, false, [], []⟩
      ]⟩,
    ⟨[11, 77111], [11, 77111], .contexts []⟩,
    ⟨[11, 77111], [11, 77111], .contexts []⟩,
    ⟨[11, 77111], [11, 77111], .contexts []⟩,
    ⟨[9, 11, 9, 11, 9, 11], [], .source 45⟩,
    ⟨[11, 9, 11, 9, 11, 9], [], .contexts [
        ⟨342, false, false, [8], [9]⟩
      ]⟩,
    ⟨[11, 9], [8, 10, 8, 10], .contexts [
        ⟨343, false, false, [], [8, 10, 8, 10]⟩
      ]⟩,
    ⟨[8, 10], [9, 11], .contexts [
        ⟨77, false, false, [], [10]⟩,
        ⟨91, false, false, [9], []⟩
      ]⟩,
    ⟨[8, 10, 8, 10], [9, 11, 9, 11], .contexts [
        ⟨345, false, false, [], [8, 10]⟩,
        ⟨77, false, false, [9, 11], [10]⟩,
        ⟨91, false, false, [9, 11, 9], []⟩
      ]⟩,
    ⟨[77111, 9], [11, 77111], .contexts [
        ⟨332, true, false, [], [9]⟩,
        ⟨344, false, false, [77109], []⟩,
        ⟨346, false, false, [77109], []⟩,
        ⟨296, false, false, [], [11, 9, 11]⟩,
        ⟨252, false, false, [], [11, 9, 11]⟩,
        ⟨253, false, false, [], [11, 9, 11]⟩,
        ⟨253, false, false, [], [11, 9, 11]⟩,
        ⟨338, false, false, [], [9, 11]⟩,
        ⟨271, false, false, [], [9, 11]⟩,
        ⟨272, false, false, [], [9, 11]⟩,
        ⟨272, false, false, [], [9, 11]⟩,
        ⟨295, false, false, [11], [11]⟩,
        ⟨328, false, false, [11], []⟩,
        ⟨339, false, false, [], []⟩,
        ⟨340, false, false, [], []⟩,
        ⟨341, false, false, [], []⟩,
        ⟨337, false, false, [11], []⟩
      ]⟩,
    ⟨[1, 77111], [1, 77111], .contexts []⟩,
    ⟨[1, 77111], [1, 77111], .contexts []⟩,
    ⟨[1, 77111], [1, 77111], .contexts []⟩,
    ⟨[11, 13, 11, 13], [], .contexts [
        ⟨135, false, false, [], []⟩
      ]⟩,
    ⟨[11, 13], [12, 10], .contexts [
        ⟨351, false, false, [], [12, 10]⟩
      ]⟩,
    ⟨[12, 10], [13, 11], .contexts [
        ⟨108, false, false, [], [10]⟩,
        ⟨91, false, false, [13], []⟩
      ]⟩,
    ⟨[77111, 13], [1, 77111], .contexts [
        ⟨332, true, false, [], [13]⟩,
        ⟨352, false, false, [77109], []⟩,
        ⟨353, false, false, [77109], []⟩,
        ⟨317, false, false, [], [11]⟩,
        ⟨318, false, false, [], [11]⟩,
        ⟨311, false, false, [], [11]⟩,
        ⟨313, false, false, [], [11]⟩,
        ⟨313, false, false, [], [11]⟩,
        ⟨328, false, false, [1], []⟩,
        ⟨348, false, false, [], []⟩,
        ⟨349, false, false, [], []⟩,
        ⟨350, false, false, [], []⟩,
        ⟨337, false, false, [1], []⟩,
        ⟨25, true, false, [], [77111]⟩
      ]⟩,
    ⟨[13, 77111], [13, 77111], .contexts []⟩,
    ⟨[13, 77111], [13, 77111], .contexts []⟩,
    ⟨[11, 15, 11, 15], [], .contexts [
        ⟨87, false, false, [], []⟩
      ]⟩,
    ⟨[11, 15], [14, 10], .contexts [
        ⟨357, false, false, [], [14, 10]⟩
      ]⟩,
    ⟨[14, 10], [15, 11], .contexts [
        ⟨20, false, false, [], [10]⟩,
        ⟨91, false, false, [15], []⟩
      ]⟩,
    ⟨[77111, 15], [77111, 15], .contexts []⟩,
    ⟨[77111, 15], [13, 77111], .contexts [
        ⟨360, false, false, [], []⟩,
        ⟨332, true, false, [], [15]⟩,
        ⟨358, false, false, [77109], []⟩,
        ⟨359, false, false, [77109], []⟩,
        ⟨325, false, false, [], [11]⟩,
        ⟨326, false, false, [], [11]⟩,
        ⟨320, false, false, [], [11]⟩,
        ⟨321, false, false, [], [11]⟩,
        ⟨321, false, false, [], [11]⟩,
        ⟨328, false, false, [13], []⟩,
        ⟨355, false, false, [], []⟩,
        ⟨356, false, false, [], []⟩,
        ⟨337, false, false, [13], []⟩,
        ⟨153, true, false, [], [77111]⟩
      ]⟩,
    ⟨[77113], [77111, 1], .source 38621⟩,
    ⟨[77111, 1], [77113], .contexts [
        ⟨362, true, false, [], []⟩
      ]⟩,
    ⟨[77113, 1], [77111], .contexts [
        ⟨363, true, false, [], [1]⟩,
        ⟨18, false, false, [77111], []⟩,
        ⟨331, false, false, [], []⟩
      ]⟩,
    ⟨[77111, 1], [77113], .contexts [
        ⟨363, false, false, [], []⟩
      ]⟩,
    ⟨[77113], [77113], .contexts []⟩,
    ⟨[77113], [77113], .contexts []⟩,
    ⟨[13, 77113], [13, 77113], .contexts []⟩,
    ⟨[13, 77113], [13, 77113], .contexts []⟩,
    ⟨[77113, 15], [77113, 15], .contexts []⟩,
    ⟨[77113], [77113], .contexts []⟩,
    ⟨[77113, 15], [13, 77113], .contexts [
        ⟨370, false, false, [], []⟩,
        ⟨367, true, false, [], [15]⟩,
        ⟨367, true, false, [], [15]⟩,
        ⟨366, true, false, [], [15]⟩,
        ⟨365, true, false, [], [15]⟩,
        ⟨199, false, false, [77111], []⟩,
        ⟨200, false, false, [77111], []⟩,
        ⟨360, false, false, [], [1]⟩,
        ⟨361, false, false, [], [1]⟩,
        ⟨355, false, false, [], [1]⟩,
        ⟨356, false, false, [], [1]⟩,
        ⟨356, false, false, [], [1]⟩,
        ⟨363, false, false, [13], []⟩,
        ⟨368, false, false, [], []⟩,
        ⟨369, false, false, [], []⟩,
        ⟨371, false, false, [13], []⟩,
        ⟨153, true, false, [], [77113]⟩
      ]⟩,
    ⟨[77115], [77113, 13], .source 38622⟩,
    ⟨[77113, 13], [77115], .contexts [
        ⟨373, true, false, [], []⟩
      ]⟩,
    ⟨[77115, 13], [77113], .contexts [
        ⟨374, true, false, [], [13]⟩,
        ⟨98, false, false, [77113], []⟩,
        ⟨367, false, false, [], []⟩
      ]⟩,
    ⟨[77113, 13], [77115], .contexts [
        ⟨374, false, false, [], []⟩
      ]⟩,
    ⟨[77115], [77115], .contexts []⟩,
    ⟨[77115], [77115], .contexts []⟩,
    ⟨[77113, 1], [77111], .contexts [
        ⟨364, false, false, [], []⟩,
        ⟨330, false, false, [], []⟩,
        ⟨331, false, false, [], []⟩,
        ⟨331, false, false, [], []⟩
      ]⟩,
    ⟨[1, 77113], [1, 77113], .contexts []⟩,
    ⟨[1, 77113], [1, 77113], .contexts []⟩,
    ⟨[1, 77113], [1, 77113], .contexts []⟩,
    ⟨[1, 77115], [1, 77115], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 006. -/
def y322TCContextRaw006 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1, 77115], [1, 77115], .contexts []⟩,
    ⟨[1, 77115], [1, 77115], .contexts []⟩,
    ⟨[13, 1, 13, 1, 13, 1], [], .contexts [
        ⟨187, false, false, [0], [1]⟩
      ]⟩,
    ⟨[13, 1], [0, 12, 0, 12], .contexts [
        ⟨386, false, false, [], [0, 12, 0, 12]⟩
      ]⟩,
    ⟨[0, 12], [1, 13], .contexts [
        ⟨19, false, false, [], [12]⟩,
        ⟨108, false, false, [1], []⟩
      ]⟩,
    ⟨[0, 12, 0], [1, 13, 1], .contexts [
        ⟨388, false, false, [], [0]⟩,
        ⟨19, false, false, [1, 13], []⟩
      ]⟩,
    ⟨[0, 12, 0, 12], [1, 13, 1, 13], .contexts [
        ⟨389, false, false, [], [12]⟩,
        ⟨108, false, false, [1, 13, 1], []⟩
      ]⟩,
    ⟨[77115, 1], [77115, 1], .contexts []⟩,
    ⟨[77115], [77115], .contexts []⟩,
    ⟨[77115, 1], [1, 77115], .contexts [
        ⟨391, false, false, [], []⟩,
        ⟨378, true, false, [], [1]⟩,
        ⟨378, true, false, [], [1]⟩,
        ⟨377, true, false, [], [1]⟩,
        ⟨376, true, false, [], [1]⟩,
        ⟨387, false, false, [77113], []⟩,
        ⟨390, false, false, [77113], []⟩,
        ⟨379, false, false, [], [13, 1, 13]⟩,
        ⟨354, false, false, [], [1, 13]⟩,
        ⟨348, false, false, [], [1, 13]⟩,
        ⟨350, false, false, [], [1, 13]⟩,
        ⟨350, false, false, [], [1, 13]⟩,
        ⟨363, false, false, [1], [13]⟩,
        ⟨380, false, false, [], [13]⟩,
        ⟨381, false, false, [], [13]⟩,
        ⟨382, false, false, [], [13]⟩,
        ⟨374, false, false, [1], []⟩,
        ⟨383, false, false, [], []⟩,
        ⟨384, false, false, [], []⟩,
        ⟨385, false, false, [], []⟩,
        ⟨392, false, false, [1], []⟩,
        ⟨25, true, false, [], [77115]⟩
      ]⟩,
    ⟨[77117], [77115, 15], .source 38623⟩,
    ⟨[77115, 15], [77117], .contexts [
        ⟨394, true, false, [], []⟩
      ]⟩,
    ⟨[77115, 15], [77117], .contexts [
        ⟨395, false, false, [], []⟩
      ]⟩,
    ⟨[77117], [77117], .contexts []⟩,
    ⟨[77117], [77117], .contexts []⟩,
    ⟨[77115, 15], [77117], .contexts [
        ⟨396, false, false, [], []⟩,
        ⟨397, false, false, [], []⟩,
        ⟨398, false, false, [], []⟩,
        ⟨398, false, false, [], []⟩
      ]⟩,
    ⟨[1, 77117], [1, 77117], .contexts []⟩,
    ⟨[1, 77117], [1, 77117], .contexts []⟩,
    ⟨[77117], [77117], .contexts []⟩,
    ⟨[77117, 1], [1, 77117], .contexts [
        ⟨399, true, false, [], [1]⟩,
        ⟨17, false, false, [77115], []⟩,
        ⟨21, false, false, [77115], []⟩,
        ⟨391, false, false, [], [15]⟩,
        ⟨393, false, false, [], [15]⟩,
        ⟨383, false, false, [], [15]⟩,
        ⟨385, false, false, [], [15]⟩,
        ⟨385, false, false, [], [15]⟩,
        ⟨395, false, false, [1], []⟩,
        ⟨400, false, false, [], []⟩,
        ⟨401, false, false, [], []⟩,
        ⟨402, false, false, [1], []⟩,
        ⟨25, true, false, [], [77117]⟩
      ]⟩,
    ⟨[77113, 15], [13, 77113], .contexts [
        ⟨372, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77117], [13, 77117], .contexts []⟩,
    ⟨[13, 77117], [13, 77117], .contexts []⟩,
    ⟨[15, 13, 15, 13, 15, 13], [], .contexts [
        ⟨146, false, false, [12], [13]⟩
      ]⟩,
    ⟨[15, 13], [12, 14, 12, 14], .contexts [
        ⟨407, false, false, [], [12, 14, 12, 14]⟩
      ]⟩,
    ⟨[12, 14, 12], [13, 15, 13], .contexts [
        ⟨108, false, false, [], [14, 12]⟩,
        ⟨20, false, false, [13], [12]⟩,
        ⟨108, false, false, [13, 15], []⟩
      ]⟩,
    ⟨[12, 14, 12, 14], [13, 15, 13, 15], .contexts [
        ⟨409, false, false, [], [14]⟩,
        ⟨20, false, false, [13, 15, 13], []⟩
      ]⟩,
    ⟨[77117, 13], [77117, 13], .contexts []⟩,
    ⟨[77117, 13], [13, 77117], .contexts [
        ⟨411, false, false, [], []⟩,
        ⟨399, true, false, [], [13]⟩,
        ⟨408, false, false, [77115], []⟩,
        ⟨410, false, false, [77115], []⟩,
        ⟨375, false, false, [], [15, 13, 15]⟩,
        ⟨366, false, false, [], [15, 13, 15]⟩,
        ⟨367, false, false, [], [15, 13, 15]⟩,
        ⟨367, false, false, [], [15, 13, 15]⟩,
        ⟨404, false, false, [], [13, 15]⟩,
        ⟨368, false, false, [], [13, 15]⟩,
        ⟨369, false, false, [], [13, 15]⟩,
        ⟨369, false, false, [], [13, 15]⟩,
        ⟨374, false, false, [13], [15]⟩,
        ⟨395, false, false, [13], []⟩,
        ⟨405, false, false, [], []⟩,
        ⟨406, false, false, [], []⟩,
        ⟨402, false, false, [13], []⟩
      ]⟩,
    ⟨[77117, 13], [13, 77117], .contexts [
        ⟨412, false, false, [], []⟩,
        ⟨153, true, false, [], [77117]⟩
      ]⟩,
    ⟨[77119], [77117, 3], .source 38624⟩,
    ⟨[77117, 3], [77119], .contexts [
        ⟨414, true, false, [], []⟩
      ]⟩,
    ⟨[77119], [77119], .contexts []⟩,
    ⟨[77119], [77119], .contexts []⟩,
    ⟨[77117, 3], [77119], .contexts [
        ⟨415, false, false, [], []⟩,
        ⟨416, false, false, [], []⟩,
        ⟨417, false, false, [], []⟩,
        ⟨417, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77119], [13, 77119], .contexts []⟩,
    ⟨[13, 77119], [13, 77119], .contexts []⟩,
    ⟨[77119, 13], [77119, 13], .contexts []⟩,
    ⟨[77119, 13], [13, 77119], .contexts [
        ⟨421, false, false, [], []⟩,
        ⟨418, true, false, [], [13]⟩,
        ⟨238, false, false, [77117], []⟩,
        ⟨239, false, false, [77117], []⟩,
        ⟨411, false, false, [], [3]⟩,
        ⟨413, false, false, [], [3]⟩,
        ⟨405, false, false, [], [3]⟩,
        ⟨406, false, false, [], [3]⟩,
        ⟨406, false, false, [], [3]⟩,
        ⟨415, false, false, [13], []⟩,
        ⟨419, false, false, [], []⟩,
        ⟨420, false, false, [], []⟩,
        ⟨153, true, false, [], [77119]⟩
      ]⟩,
    ⟨[77121], [77119, 5], .source 38625⟩,
    ⟨[77119, 5], [77121], .contexts [
        ⟨423, true, false, [], []⟩
      ]⟩,
    ⟨[77121], [77121], .contexts []⟩,
    ⟨[77119, 13], [13, 77119], .contexts [
        ⟨421, false, false, [], []⟩,
        ⟨422, false, false, [], []⟩,
        ⟨419, false, false, [], []⟩,
        ⟨420, false, false, [], []⟩,
        ⟨420, false, false, [], []⟩
      ]⟩,
    ⟨[77123], [77121, 1], .source 38626⟩,
    ⟨[77121, 1], [77123], .contexts [
        ⟨427, true, false, [], []⟩
      ]⟩,
    ⟨[77123, 1], [77121], .contexts [
        ⟨428, true, false, [], [1]⟩,
        ⟨18, false, false, [77121], []⟩,
        ⟨425, false, false, [], []⟩
      ]⟩,
    ⟨[77125], [77123, 9], .source 38627⟩,
    ⟨[77123, 9], [77125], .contexts [
        ⟨430, true, false, [], []⟩
      ]⟩,
    ⟨[77123], [77123], .contexts []⟩,
    ⟨[77127], [77125, 11], .source 38628⟩,
    ⟨[77125, 11], [77127], .contexts [
        ⟨433, true, false, [], []⟩
      ]⟩,
    ⟨[77125], [77125], .contexts []⟩,
    ⟨[77129], [77127, 1], .source 38629⟩,
    ⟨[77127, 1], [77129], .contexts [
        ⟨436, true, false, [], []⟩
      ]⟩,
    ⟨[77127], [77127], .contexts []⟩,
    ⟨[77129, 1], [77127], .contexts [
        ⟨437, true, false, [], [1]⟩,
        ⟨18, false, false, [77127], []⟩,
        ⟨438, false, false, [], []⟩
      ]⟩,
    ⟨[77131], [77129, 13], .source 38630⟩,
    ⟨[77129, 13], [77131], .contexts [
        ⟨440, true, false, [], []⟩
      ]⟩,
    ⟨[77129], [77129], .contexts []⟩,
    ⟨[77131, 13], [77129], .contexts [
        ⟨441, true, false, [], [13]⟩,
        ⟨98, false, false, [77129], []⟩,
        ⟨442, false, false, [], []⟩
      ]⟩,
    ⟨[77133], [77131, 15], .source 38631⟩,
    ⟨[77131, 15], [77133], .contexts [
        ⟨444, true, false, [], []⟩
      ]⟩,
    ⟨[77131], [77131], .contexts []⟩,
    ⟨[77135], [77133, 1], .source 38632⟩]

/-- Exact literal claimed equations and contextual derivations, block 007. -/
def y322TCContextRaw007 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77133, 1], [77135], .contexts [
        ⟨447, true, false, [], []⟩
      ]⟩,
    ⟨[77133], [77133], .contexts []⟩,
    ⟨[77135, 1], [77133], .contexts [
        ⟨448, true, false, [], [1]⟩,
        ⟨18, false, false, [77133], []⟩,
        ⟨449, false, false, [], []⟩
      ]⟩,
    ⟨[77137], [77135, 3], .source 38633⟩,
    ⟨[77135, 3], [77137], .contexts [
        ⟨451, true, false, [], []⟩
      ]⟩,
    ⟨[77135], [77135], .contexts []⟩,
    ⟨[77137, 3], [77135], .contexts [
        ⟨452, true, false, [], [3]⟩,
        ⟨35, false, false, [77135], []⟩,
        ⟨453, false, false, [], []⟩
      ]⟩,
    ⟨[77139], [77137, 5], .source 38634⟩,
    ⟨[77137, 5], [77139], .contexts [
        ⟨455, true, false, [], []⟩
      ]⟩,
    ⟨[77137], [77137], .contexts []⟩,
    ⟨[77141], [77139, 1], .source 38635⟩,
    ⟨[77139, 1], [77141], .contexts [
        ⟨458, true, false, [], []⟩
      ]⟩,
    ⟨[77139], [77139], .contexts []⟩,
    ⟨[77143], [77141, 9], .source 38636⟩,
    ⟨[77141, 9], [77143], .contexts [
        ⟨461, true, false, [], []⟩
      ]⟩,
    ⟨[77141], [77141], .contexts []⟩,
    ⟨[77143, 9], [77141], .contexts [
        ⟨462, true, false, [], [9]⟩,
        ⟨76, false, false, [77141], []⟩,
        ⟨463, false, false, [], []⟩
      ]⟩,
    ⟨[77145], [77143, 11], .source 38637⟩,
    ⟨[77143, 11], [77145], .contexts [
        ⟨465, true, false, [], []⟩
      ]⟩,
    ⟨[77143], [77143], .contexts []⟩,
    ⟨[77147], [77145, 1], .source 38638⟩,
    ⟨[77145, 1], [77147], .contexts [
        ⟨468, true, false, [], []⟩
      ]⟩,
    ⟨[77145], [77145], .contexts []⟩,
    ⟨[77147, 1], [77145], .contexts [
        ⟨469, true, false, [], [1]⟩,
        ⟨18, false, false, [77145], []⟩,
        ⟨470, false, false, [], []⟩
      ]⟩,
    ⟨[77149], [77147, 13], .source 38639⟩,
    ⟨[77147, 13], [77149], .contexts [
        ⟨472, true, false, [], []⟩
      ]⟩,
    ⟨[77147], [77147], .contexts []⟩,
    ⟨[77151], [77149, 15], .source 38640⟩,
    ⟨[77149, 15], [77151], .contexts [
        ⟨475, true, false, [], []⟩
      ]⟩,
    ⟨[77149], [77149], .contexts []⟩,
    ⟨[77153], [77151, 1], .source 38641⟩,
    ⟨[77151, 1], [77153], .contexts [
        ⟨478, true, false, [], []⟩
      ]⟩,
    ⟨[77151], [77151], .contexts []⟩,
    ⟨[77153, 1], [77151], .contexts [
        ⟨479, true, false, [], [1]⟩,
        ⟨18, false, false, [77151], []⟩,
        ⟨480, false, false, [], []⟩
      ]⟩,
    ⟨[77155], [77153, 3], .source 38642⟩,
    ⟨[77153, 3], [77155], .contexts [
        ⟨482, true, false, [], []⟩
      ]⟩,
    ⟨[77153], [77153], .contexts []⟩,
    ⟨[77157], [77155, 5], .source 38643⟩,
    ⟨[77155, 5], [77157], .contexts [
        ⟨485, true, false, [], []⟩
      ]⟩,
    ⟨[77155], [77155], .contexts []⟩,
    ⟨[77159], [77157, 1], .source 38644⟩,
    ⟨[77157, 1], [77159], .contexts [
        ⟨488, true, false, [], []⟩
      ]⟩,
    ⟨[77157], [77157], .contexts []⟩,
    ⟨[77159, 1], [77157], .contexts [
        ⟨489, true, false, [], [1]⟩,
        ⟨18, false, false, [77157], []⟩,
        ⟨490, false, false, [], []⟩
      ]⟩,
    ⟨[77161], [77159, 9], .source 38645⟩,
    ⟨[77159, 9], [77161], .contexts [
        ⟨492, true, false, [], []⟩
      ]⟩,
    ⟨[77159], [77159], .contexts []⟩,
    ⟨[77163], [77161, 11], .source 38646⟩,
    ⟨[77161, 11], [77163], .contexts [
        ⟨495, true, false, [], []⟩
      ]⟩,
    ⟨[77161], [77161], .contexts []⟩,
    ⟨[77165], [77163, 1], .source 38647⟩,
    ⟨[77163, 1], [77165], .contexts [
        ⟨498, true, false, [], []⟩
      ]⟩,
    ⟨[77163], [77163], .contexts []⟩,
    ⟨[77165, 1], [77163], .contexts [
        ⟨499, true, false, [], [1]⟩,
        ⟨18, false, false, [77163], []⟩,
        ⟨500, false, false, [], []⟩
      ]⟩,
    ⟨[77167], [77165, 13], .source 38648⟩,
    ⟨[77165, 13], [77167], .contexts [
        ⟨502, true, false, [], []⟩
      ]⟩,
    ⟨[77165], [77165], .contexts []⟩,
    ⟨[77167, 13], [77165], .contexts [
        ⟨503, true, false, [], [13]⟩,
        ⟨98, false, false, [77165], []⟩,
        ⟨504, false, false, [], []⟩
      ]⟩,
    ⟨[77169], [77167, 15], .source 38649⟩,
    ⟨[77167, 15], [77169], .contexts [
        ⟨506, true, false, [], []⟩
      ]⟩,
    ⟨[77167], [77167], .contexts []⟩,
    ⟨[77169, 15], [77167], .contexts [
        ⟨507, true, false, [], [15]⟩,
        ⟨3, false, false, [77167], []⟩,
        ⟨508, false, false, [], []⟩
      ]⟩,
    ⟨[77171], [77169, 1], .source 38650⟩,
    ⟨[77169, 1], [77171], .contexts [
        ⟨510, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 008. -/
def y322TCContextRaw008 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77169], [77169], .contexts []⟩,
    ⟨[77173], [77171, 3], .source 38651⟩,
    ⟨[77171, 3], [77173], .contexts [
        ⟨513, true, false, [], []⟩
      ]⟩,
    ⟨[77171], [77171], .contexts []⟩,
    ⟨[77175], [77173, 5], .source 38652⟩,
    ⟨[77173, 5], [77175], .contexts [
        ⟨516, true, false, [], []⟩
      ]⟩,
    ⟨[77173], [77173], .contexts []⟩,
    ⟨[77177], [77175, 1], .source 38653⟩,
    ⟨[77175, 1], [77177], .contexts [
        ⟨519, true, false, [], []⟩
      ]⟩,
    ⟨[77175], [77175], .contexts []⟩,
    ⟨[77177, 1], [77175], .contexts [
        ⟨520, true, false, [], [1]⟩,
        ⟨18, false, false, [77175], []⟩,
        ⟨521, false, false, [], []⟩
      ]⟩,
    ⟨[77179], [77177, 9], .source 38654⟩,
    ⟨[77177, 9], [77179], .contexts [
        ⟨523, true, false, [], []⟩
      ]⟩,
    ⟨[77177], [77177], .contexts []⟩,
    ⟨[77181], [77179, 11], .source 38655⟩,
    ⟨[77179, 11], [77181], .contexts [
        ⟨526, true, false, [], []⟩
      ]⟩,
    ⟨[77179], [77179], .contexts []⟩,
    ⟨[77183], [77181, 1], .source 38656⟩,
    ⟨[77181, 1], [77183], .contexts [
        ⟨529, true, false, [], []⟩
      ]⟩,
    ⟨[77181], [77181], .contexts []⟩,
    ⟨[77183, 1], [77181], .contexts [
        ⟨530, true, false, [], [1]⟩,
        ⟨18, false, false, [77181], []⟩,
        ⟨531, false, false, [], []⟩
      ]⟩,
    ⟨[77185], [77183, 13], .source 38657⟩,
    ⟨[77183, 13], [77185], .contexts [
        ⟨533, true, false, [], []⟩
      ]⟩,
    ⟨[77183], [77183], .contexts []⟩,
    ⟨[77187], [77185, 15], .source 38658⟩,
    ⟨[77185, 15], [77187], .contexts [
        ⟨536, true, false, [], []⟩
      ]⟩,
    ⟨[77185], [77185], .contexts []⟩,
    ⟨[77187, 15], [77185], .contexts [
        ⟨537, true, false, [], [15]⟩,
        ⟨3, false, false, [77185], []⟩,
        ⟨538, false, false, [], []⟩
      ]⟩,
    ⟨[77189], [77187, 1], .source 38659⟩,
    ⟨[77187, 1], [77189], .contexts [
        ⟨540, true, false, [], []⟩
      ]⟩,
    ⟨[77187], [77187], .contexts []⟩,
    ⟨[77189, 1], [77187], .contexts [
        ⟨541, true, false, [], [1]⟩,
        ⟨18, false, false, [77187], []⟩,
        ⟨542, false, false, [], []⟩
      ]⟩,
    ⟨[77191], [77189, 3], .source 38660⟩,
    ⟨[77189, 3], [77191], .contexts [
        ⟨544, true, false, [], []⟩
      ]⟩,
    ⟨[77189], [77189], .contexts []⟩,
    ⟨[77191, 3], [77189], .contexts [
        ⟨545, true, false, [], [3]⟩,
        ⟨35, false, false, [77189], []⟩,
        ⟨546, false, false, [], []⟩
      ]⟩,
    ⟨[77193], [77191, 5], .source 38661⟩,
    ⟨[77191, 5], [77193], .contexts [
        ⟨548, true, false, [], []⟩
      ]⟩,
    ⟨[77191], [77191], .contexts []⟩,
    ⟨[77193, 5], [77191], .contexts [
        ⟨549, true, false, [], [5]⟩,
        ⟨49, false, false, [77191], []⟩,
        ⟨550, false, false, [], []⟩
      ]⟩,
    ⟨[77195], [77193, 1], .source 38662⟩,
    ⟨[77193, 1], [77195], .contexts [
        ⟨552, true, false, [], []⟩
      ]⟩,
    ⟨[77193], [77193], .contexts []⟩,
    ⟨[77195, 1], [77193], .contexts [
        ⟨553, true, false, [], [1]⟩,
        ⟨18, false, false, [77193], []⟩,
        ⟨554, false, false, [], []⟩
      ]⟩,
    ⟨[77197], [77195, 9], .source 38663⟩,
    ⟨[77195, 9], [77197], .contexts [
        ⟨556, true, false, [], []⟩
      ]⟩,
    ⟨[77195], [77195], .contexts []⟩,
    ⟨[77197, 9], [77195], .contexts [
        ⟨557, true, false, [], [9]⟩,
        ⟨76, false, false, [77195], []⟩,
        ⟨558, false, false, [], []⟩
      ]⟩,
    ⟨[77199], [77197, 11], .source 38664⟩,
    ⟨[77197, 11], [77199], .contexts [
        ⟨560, true, false, [], []⟩
      ]⟩,
    ⟨[77197], [77197], .contexts []⟩,
    ⟨[77199, 11], [77197], .contexts [
        ⟨561, true, false, [], [11]⟩,
        ⟨90, false, false, [77197], []⟩,
        ⟨562, false, false, [], []⟩
      ]⟩,
    ⟨[77201], [77199, 1], .source 38665⟩,
    ⟨[77199], [77199], .contexts []⟩,
    ⟨[77201, 1], [77199], .contexts [
        ⟨564, false, false, [], [1]⟩,
        ⟨18, false, false, [77199], []⟩,
        ⟨565, false, false, [], []⟩
      ]⟩,
    ⟨[77203], [77201, 13], .source 38666⟩,
    ⟨[77201, 13], [77203], .contexts [
        ⟨567, true, false, [], []⟩
      ]⟩,
    ⟨[77201], [77201], .contexts []⟩,
    ⟨[77203, 13], [77201], .contexts [
        ⟨568, true, false, [], [13]⟩,
        ⟨98, false, false, [77201], []⟩,
        ⟨569, false, false, [], []⟩
      ]⟩,
    ⟨[77205], [77203, 15], .source 38667⟩,
    ⟨[77203, 15], [77205], .contexts [
        ⟨571, true, false, [], []⟩
      ]⟩,
    ⟨[77203], [77203], .contexts []⟩,
    ⟨[77205, 15], [77203], .contexts [
        ⟨572, true, false, [], [15]⟩,
        ⟨3, false, false, [77203], []⟩,
        ⟨573, false, false, [], []⟩
      ]⟩,
    ⟨[77207], [77205, 1], .source 38668⟩]

/-- Exact literal claimed equations and contextual derivations, block 009. -/
def y322TCContextRaw009 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77205, 1], [77207], .contexts [
        ⟨575, true, false, [], []⟩
      ]⟩,
    ⟨[77205], [77205], .contexts []⟩,
    ⟨[77207, 1], [77205], .contexts [
        ⟨576, true, false, [], [1]⟩,
        ⟨18, false, false, [77205], []⟩,
        ⟨577, false, false, [], []⟩
      ]⟩,
    ⟨[77209], [77207, 3], .source 38669⟩,
    ⟨[77207], [77207], .contexts []⟩,
    ⟨[77209, 3], [77207], .contexts [
        ⟨579, false, false, [], [3]⟩,
        ⟨35, false, false, [77207], []⟩,
        ⟨580, false, false, [], []⟩
      ]⟩,
    ⟨[77211], [77209, 5], .source 38670⟩,
    ⟨[77209, 5], [77211], .contexts [
        ⟨582, true, false, [], []⟩
      ]⟩,
    ⟨[77209], [77209], .contexts []⟩,
    ⟨[77211, 5], [77209], .contexts [
        ⟨583, true, false, [], [5]⟩,
        ⟨49, false, false, [77209], []⟩,
        ⟨584, false, false, [], []⟩
      ]⟩,
    ⟨[77213], [77211, 1], .source 38671⟩,
    ⟨[77211, 1], [77213], .contexts [
        ⟨586, true, false, [], []⟩
      ]⟩,
    ⟨[77211], [77211], .contexts []⟩,
    ⟨[77213, 1], [77211], .contexts [
        ⟨587, true, false, [], [1]⟩,
        ⟨18, false, false, [77211], []⟩,
        ⟨588, false, false, [], []⟩
      ]⟩,
    ⟨[77215], [77213, 9], .source 38672⟩,
    ⟨[77213, 9], [77215], .contexts [
        ⟨590, true, false, [], []⟩
      ]⟩,
    ⟨[77213], [77213], .contexts []⟩,
    ⟨[77215, 9], [77213], .contexts [
        ⟨591, true, false, [], [9]⟩,
        ⟨76, false, false, [77213], []⟩,
        ⟨592, false, false, [], []⟩
      ]⟩,
    ⟨[77217], [77215, 11], .source 38673⟩,
    ⟨[77215, 11], [77217], .contexts [
        ⟨594, true, false, [], []⟩
      ]⟩,
    ⟨[77215], [77215], .contexts []⟩,
    ⟨[77217, 11], [77215], .contexts [
        ⟨595, true, false, [], [11]⟩,
        ⟨90, false, false, [77215], []⟩,
        ⟨596, false, false, [], []⟩
      ]⟩,
    ⟨[77219], [77217, 1], .source 38674⟩,
    ⟨[77217, 1], [77219], .contexts [
        ⟨598, true, false, [], []⟩
      ]⟩,
    ⟨[77217], [77217], .contexts []⟩,
    ⟨[77219, 1], [77217], .contexts [
        ⟨599, true, false, [], [1]⟩,
        ⟨18, false, false, [77217], []⟩,
        ⟨600, false, false, [], []⟩
      ]⟩,
    ⟨[77221], [77219, 13], .source 38675⟩,
    ⟨[77219], [77219], .contexts []⟩,
    ⟨[77221, 13], [77219], .contexts [
        ⟨602, false, false, [], [13]⟩,
        ⟨98, false, false, [77219], []⟩,
        ⟨603, false, false, [], []⟩
      ]⟩,
    ⟨[77223], [77221, 15], .source 38676⟩,
    ⟨[77221, 15], [77223], .contexts [
        ⟨605, true, false, [], []⟩
      ]⟩,
    ⟨[77221], [77221], .contexts []⟩,
    ⟨[77223, 15], [77221], .contexts [
        ⟨606, true, false, [], [15]⟩,
        ⟨3, false, false, [77221], []⟩,
        ⟨607, false, false, [], []⟩
      ]⟩,
    ⟨[77225], [77223, 1], .source 38677⟩,
    ⟨[77223], [77223], .contexts []⟩,
    ⟨[77225, 1], [77223], .contexts [
        ⟨609, false, false, [], [1]⟩,
        ⟨18, false, false, [77223], []⟩,
        ⟨610, false, false, [], []⟩
      ]⟩,
    ⟨[77227], [77225, 3], .source 38678⟩,
    ⟨[77225, 3], [77227], .contexts [
        ⟨612, true, false, [], []⟩
      ]⟩,
    ⟨[77225], [77225], .contexts []⟩,
    ⟨[77227, 3], [77225], .contexts [
        ⟨613, true, false, [], [3]⟩,
        ⟨35, false, false, [77225], []⟩,
        ⟨614, false, false, [], []⟩
      ]⟩,
    ⟨[77229], [77227, 5], .source 38679⟩,
    ⟨[77227, 5], [77229], .contexts [
        ⟨616, true, false, [], []⟩
      ]⟩,
    ⟨[77227], [77227], .contexts []⟩,
    ⟨[77229, 5], [77227], .contexts [
        ⟨617, true, false, [], [5]⟩,
        ⟨49, false, false, [77227], []⟩,
        ⟨618, false, false, [], []⟩
      ]⟩,
    ⟨[77231], [77229, 1], .source 38680⟩,
    ⟨[77229, 1], [77231], .contexts [
        ⟨620, true, false, [], []⟩
      ]⟩,
    ⟨[77229], [77229], .contexts []⟩,
    ⟨[77231], [77231], .contexts []⟩,
    ⟨[77227], [77227], .contexts []⟩,
    ⟨[77227, 3], [77225], .contexts [
        ⟨615, false, false, [], []⟩
      ]⟩,
    ⟨[77225], [77225], .contexts []⟩,
    ⟨[77225, 1], [77223], .contexts [
        ⟨611, false, false, [], []⟩
      ]⟩,
    ⟨[77223], [77223], .contexts []⟩,
    ⟨[77223, 15], [77221], .contexts [
        ⟨608, false, false, [], []⟩
      ]⟩,
    ⟨[77221], [77221], .contexts []⟩,
    ⟨[77221, 13], [77219], .contexts [
        ⟨604, false, false, [], []⟩
      ]⟩,
    ⟨[77219], [77219], .contexts []⟩,
    ⟨[77229, 5, 3, 1, 15, 13], [77219], .contexts [
        ⟨619, false, false, [], [3, 1, 15, 13]⟩,
        ⟨624, false, false, [], [3, 1, 15, 13]⟩,
        ⟨618, false, false, [], [3, 1, 15, 13]⟩,
        ⟨618, false, false, [], [3, 1, 15, 13]⟩,
        ⟨625, false, false, [], [1, 15, 13]⟩,
        ⟨626, false, false, [], [1, 15, 13]⟩,
        ⟨614, false, false, [], [1, 15, 13]⟩,
        ⟨614, false, false, [], [1, 15, 13]⟩,
        ⟨627, false, false, [], [15, 13]⟩,
        ⟨628, false, false, [], [15, 13]⟩,
        ⟨610, false, false, [], [15, 13]⟩,
        ⟨610, false, false, [], [15, 13]⟩,
        ⟨629, false, false, [], [13]⟩,
        ⟨630, false, false, [], [13]⟩,
        ⟨607, false, false, [], [13]⟩,
        ⟨607, false, false, [], [13]⟩,
        ⟨631, false, false, [], []⟩,
        ⟨632, false, false, [], []⟩,
        ⟨603, false, false, [], []⟩,
        ⟨603, false, false, [], []⟩
      ]⟩,
    ⟨[77217, 11], [77215], .contexts [
        ⟨597, false, false, [], []⟩
      ]⟩,
    ⟨[77215], [77215], .contexts []⟩,
    ⟨[77215, 9], [77213], .contexts [
        ⟨593, false, false, [], []⟩
      ]⟩,
    ⟨[77213], [77213], .contexts []⟩,
    ⟨[77213, 1], [77211], .contexts [
        ⟨589, false, false, [], []⟩
      ]⟩,
    ⟨[77211], [77211], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 010. -/
def y322TCContextRaw010 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77211, 5], [77209], .contexts [
        ⟨585, false, false, [], []⟩
      ]⟩,
    ⟨[77209], [77209], .contexts []⟩,
    ⟨[77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [77209], .contexts [
        ⟨633, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨601, false, false, [], [11, 9, 1, 5]⟩,
        ⟨600, false, false, [], [11, 9, 1, 5]⟩,
        ⟨600, false, false, [], [11, 9, 1, 5]⟩,
        ⟨634, false, false, [], [9, 1, 5]⟩,
        ⟨635, false, false, [], [9, 1, 5]⟩,
        ⟨596, false, false, [], [9, 1, 5]⟩,
        ⟨596, false, false, [], [9, 1, 5]⟩,
        ⟨636, false, false, [], [1, 5]⟩,
        ⟨637, false, false, [], [1, 5]⟩,
        ⟨592, false, false, [], [1, 5]⟩,
        ⟨592, false, false, [], [1, 5]⟩,
        ⟨638, false, false, [], [5]⟩,
        ⟨639, false, false, [], [5]⟩,
        ⟨588, false, false, [], [5]⟩,
        ⟨588, false, false, [], [5]⟩,
        ⟨640, false, false, [], []⟩,
        ⟨641, false, false, [], []⟩,
        ⟨584, false, false, [], []⟩,
        ⟨584, false, false, [], []⟩
      ]⟩,
    ⟨[77209, 3], [77207], .contexts [
        ⟨581, false, false, [], []⟩
      ]⟩,
    ⟨[77207], [77207], .contexts []⟩,
    ⟨[77207, 1], [77205], .contexts [
        ⟨578, false, false, [], []⟩
      ]⟩,
    ⟨[77205], [77205], .contexts []⟩,
    ⟨[77205, 15], [77203], .contexts [
        ⟨574, false, false, [], []⟩
      ]⟩,
    ⟨[77203], [77203], .contexts []⟩,
    ⟨[77203, 13], [77201], .contexts [
        ⟨570, false, false, [], []⟩
      ]⟩,
    ⟨[77201], [77201], .contexts []⟩,
    ⟨[77201, 1], [77199], .contexts [
        ⟨566, false, false, [], []⟩
      ]⟩,
    ⟨[77199], [77199], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [77199], .contexts [
        ⟨642, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨643, false, false, [], [1, 15, 13, 1]⟩,
        ⟨644, false, false, [], [1, 15, 13, 1]⟩,
        ⟨580, false, false, [], [1, 15, 13, 1]⟩,
        ⟨580, false, false, [], [1, 15, 13, 1]⟩,
        ⟨645, false, false, [], [15, 13, 1]⟩,
        ⟨646, false, false, [], [15, 13, 1]⟩,
        ⟨577, false, false, [], [15, 13, 1]⟩,
        ⟨577, false, false, [], [15, 13, 1]⟩,
        ⟨647, false, false, [], [13, 1]⟩,
        ⟨648, false, false, [], [13, 1]⟩,
        ⟨573, false, false, [], [13, 1]⟩,
        ⟨573, false, false, [], [13, 1]⟩,
        ⟨649, false, false, [], [1]⟩,
        ⟨650, false, false, [], [1]⟩,
        ⟨569, false, false, [], [1]⟩,
        ⟨569, false, false, [], [1]⟩,
        ⟨651, false, false, [], []⟩,
        ⟨652, false, false, [], []⟩,
        ⟨565, false, false, [], []⟩,
        ⟨565, false, false, [], []⟩
      ]⟩,
    ⟨[77197, 9], [77195], .contexts [
        ⟨559, false, false, [], []⟩
      ]⟩,
    ⟨[77195], [77195], .contexts []⟩,
    ⟨[77193], [77193], .contexts []⟩,
    ⟨[77193, 5], [77191], .contexts [
        ⟨551, false, false, [], []⟩
      ]⟩,
    ⟨[77191], [77191], .contexts []⟩,
    ⟨[77191, 3], [77189], .contexts [
        ⟨547, false, false, [], []⟩
      ]⟩,
    ⟨[77189], [77189], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [77189], .contexts [
        ⟨653, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨563, false, false, [], [9, 1, 5, 3]⟩,
        ⟨562, false, false, [], [9, 1, 5, 3]⟩,
        ⟨562, false, false, [], [9, 1, 5, 3]⟩,
        ⟨654, false, false, [], [1, 5, 3]⟩,
        ⟨655, false, false, [], [1, 5, 3]⟩,
        ⟨558, false, false, [], [1, 5, 3]⟩,
        ⟨558, false, false, [], [1, 5, 3]⟩,
        ⟨555, false, false, [], [5, 3]⟩,
        ⟨656, false, false, [], [5, 3]⟩,
        ⟨554, false, false, [], [5, 3]⟩,
        ⟨554, false, false, [], [5, 3]⟩,
        ⟨657, false, false, [], [3]⟩,
        ⟨658, false, false, [], [3]⟩,
        ⟨550, false, false, [], [3]⟩,
        ⟨550, false, false, [], [3]⟩,
        ⟨659, false, false, [], []⟩,
        ⟨660, false, false, [], []⟩,
        ⟨546, false, false, [], []⟩,
        ⟨546, false, false, [], []⟩
      ]⟩,
    ⟨[77189, 1], [77187], .contexts [
        ⟨543, false, false, [], []⟩
      ]⟩,
    ⟨[77187], [77187], .contexts []⟩,
    ⟨[77185], [77185], .contexts []⟩,
    ⟨[77185, 13], [77183], .contexts [
        ⟨534, true, false, [], [13]⟩,
        ⟨98, false, false, [77183], []⟩,
        ⟨535, false, false, [], []⟩
      ]⟩,
    ⟨[77183], [77183], .contexts []⟩,
    ⟨[77183, 1], [77181], .contexts [
        ⟨532, false, false, [], []⟩
      ]⟩,
    ⟨[77181], [77181], .contexts []⟩,
    ⟨[77181, 11], [77179], .contexts [
        ⟨527, true, false, [], [11]⟩,
        ⟨90, false, false, [77179], []⟩,
        ⟨528, false, false, [], []⟩
      ]⟩,
    ⟨[77179], [77179], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [77179], .contexts [
        ⟨661, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨662, false, false, [], [15, 13, 1, 11]⟩,
        ⟨663, false, false, [], [15, 13, 1, 11]⟩,
        ⟨542, false, false, [], [15, 13, 1, 11]⟩,
        ⟨542, false, false, [], [15, 13, 1, 11]⟩,
        ⟨539, false, false, [], [13, 1, 11]⟩,
        ⟨664, false, false, [], [13, 1, 11]⟩,
        ⟨538, false, false, [], [13, 1, 11]⟩,
        ⟨538, false, false, [], [13, 1, 11]⟩,
        ⟨665, false, false, [], [1, 11]⟩,
        ⟨666, false, false, [], [1, 11]⟩,
        ⟨535, false, false, [], [1, 11]⟩,
        ⟨535, false, false, [], [1, 11]⟩,
        ⟨667, false, false, [], [11]⟩,
        ⟨668, false, false, [], [11]⟩,
        ⟨531, false, false, [], [11]⟩,
        ⟨531, false, false, [], [11]⟩,
        ⟨669, false, false, [], []⟩,
        ⟨670, false, false, [], []⟩,
        ⟨528, false, false, [], []⟩,
        ⟨528, false, false, [], []⟩
      ]⟩,
    ⟨[77179, 9], [77177], .contexts [
        ⟨524, true, false, [], [9]⟩,
        ⟨76, false, false, [77177], []⟩,
        ⟨525, false, false, [], []⟩
      ]⟩,
    ⟨[77177], [77177], .contexts []⟩,
    ⟨[77177, 1], [77175], .contexts [
        ⟨522, false, false, [], []⟩
      ]⟩,
    ⟨[77175], [77175], .contexts []⟩,
    ⟨[77175, 5], [77173], .contexts [
        ⟨517, true, false, [], [5]⟩,
        ⟨49, false, false, [77173], []⟩,
        ⟨518, false, false, [], []⟩
      ]⟩,
    ⟨[77173], [77173], .contexts []⟩,
    ⟨[77173, 3], [77171], .contexts [
        ⟨514, true, false, [], [3]⟩,
        ⟨35, false, false, [77171], []⟩,
        ⟨515, false, false, [], []⟩
      ]⟩,
    ⟨[77171], [77171], .contexts []⟩,
    ⟨[77171, 1], [77169], .contexts [
        ⟨511, true, false, [], [1]⟩,
        ⟨18, false, false, [77169], []⟩,
        ⟨512, false, false, [], []⟩
      ]⟩,
    ⟨[77169], [77169], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1
    ], [77169], .contexts [
        ⟨671, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨672, false, false, [], [1, 5, 3, 1]⟩,
        ⟨673, false, false, [], [1, 5, 3, 1]⟩,
        ⟨525, false, false, [], [1, 5, 3, 1]⟩,
        ⟨525, false, false, [], [1, 5, 3, 1]⟩,
        ⟨674, false, false, [], [5, 3, 1]⟩,
        ⟨675, false, false, [], [5, 3, 1]⟩,
        ⟨521, false, false, [], [5, 3, 1]⟩,
        ⟨521, false, false, [], [5, 3, 1]⟩,
        ⟨676, false, false, [], [3, 1]⟩,
        ⟨677, false, false, [], [3, 1]⟩,
        ⟨518, false, false, [], [3, 1]⟩,
        ⟨518, false, false, [], [3, 1]⟩,
        ⟨678, false, false, [], [1]⟩,
        ⟨679, false, false, [], [1]⟩,
        ⟨515, false, false, [], [1]⟩,
        ⟨515, false, false, [], [1]⟩,
        ⟨680, false, false, [], []⟩,
        ⟨681, false, false, [], []⟩,
        ⟨512, false, false, [], []⟩,
        ⟨512, false, false, [], []⟩
      ]⟩,
    ⟨[77167], [77167], .contexts []⟩,
    ⟨[77167, 13], [77165], .contexts [
        ⟨505, false, false, [], []⟩
      ]⟩,
    ⟨[77165], [77165], .contexts []⟩,
    ⟨[77165, 1], [77163], .contexts [
        ⟨501, false, false, [], []⟩
      ]⟩,
    ⟨[77163], [77163], .contexts []⟩,
    ⟨[77163, 11], [77161], .contexts [
        ⟨496, true, false, [], [11]⟩,
        ⟨90, false, false, [77161], []⟩,
        ⟨497, false, false, [], []⟩
      ]⟩,
    ⟨[77161], [77161], .contexts []⟩,
    ⟨[77161, 9], [77159], .contexts [
        ⟨493, true, false, [], [9]⟩,
        ⟨76, false, false, [77159], []⟩,
        ⟨494, false, false, [], []⟩
      ]⟩,
    ⟨[77159], [77159], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [77159], .contexts [
        ⟨682, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨509, false, false, [], [13, 1, 11, 9]⟩,
        ⟨683, false, false, [], [13, 1, 11, 9]⟩,
        ⟨508, false, false, [], [13, 1, 11, 9]⟩,
        ⟨508, false, false, [], [13, 1, 11, 9]⟩,
        ⟨684, false, false, [], [1, 11, 9]⟩,
        ⟨685, false, false, [], [1, 11, 9]⟩,
        ⟨504, false, false, [], [1, 11, 9]⟩,
        ⟨504, false, false, [], [1, 11, 9]⟩,
        ⟨686, false, false, [], [11, 9]⟩,
        ⟨687, false, false, [], [11, 9]⟩,
        ⟨500, false, false, [], [11, 9]⟩,
        ⟨500, false, false, [], [11, 9]⟩,
        ⟨688, false, false, [], [9]⟩,
        ⟨689, false, false, [], [9]⟩,
        ⟨497, false, false, [], [9]⟩,
        ⟨497, false, false, [], [9]⟩,
        ⟨690, false, false, [], []⟩,
        ⟨691, false, false, [], []⟩,
        ⟨494, false, false, [], []⟩,
        ⟨494, false, false, [], []⟩
      ]⟩,
    ⟨[77159, 1], [77157], .contexts [
        ⟨491, false, false, [], []⟩
      ]⟩,
    ⟨[77157], [77157], .contexts []⟩,
    ⟨[77157, 5], [77155], .contexts [
        ⟨486, true, false, [], [5]⟩,
        ⟨49, false, false, [77155], []⟩,
        ⟨487, false, false, [], []⟩
      ]⟩,
    ⟨[77155], [77155], .contexts []⟩,
    ⟨[77155, 3], [77153], .contexts [
        ⟨483, true, false, [], [3]⟩,
        ⟨35, false, false, [77153], []⟩,
        ⟨484, false, false, [], []⟩
      ]⟩,
    ⟨[77153], [77153], .contexts []⟩,
    ⟨[77153, 1], [77151], .contexts [
        ⟨481, false, false, [], []⟩
      ]⟩,
    ⟨[77151], [77151], .contexts []⟩,
    ⟨[77149], [77149], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [77149], .contexts [
        ⟨692, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨693, false, false, [], [5, 3, 1, 15]⟩,
        ⟨694, false, false, [], [5, 3, 1, 15]⟩,
        ⟨490, false, false, [], [5, 3, 1, 15]⟩,
        ⟨490, false, false, [], [5, 3, 1, 15]⟩,
        ⟨695, false, false, [], [3, 1, 15]⟩,
        ⟨696, false, false, [], [3, 1, 15]⟩,
        ⟨487, false, false, [], [3, 1, 15]⟩,
        ⟨487, false, false, [], [3, 1, 15]⟩,
        ⟨697, false, false, [], [1, 15]⟩,
        ⟨698, false, false, [], [1, 15]⟩,
        ⟨484, false, false, [], [1, 15]⟩,
        ⟨484, false, false, [], [1, 15]⟩,
        ⟨699, false, false, [], [15]⟩,
        ⟨700, false, false, [], [15]⟩,
        ⟨480, false, false, [], [15]⟩,
        ⟨480, false, false, [], [15]⟩,
        ⟨476, true, false, [], [15]⟩,
        ⟨3, false, false, [77149], []⟩,
        ⟨477, false, false, [], []⟩,
        ⟨701, false, false, [], []⟩,
        ⟨477, false, false, [], []⟩,
        ⟨477, false, false, [], []⟩
      ]⟩,
    ⟨[77149, 13], [77147], .contexts [
        ⟨473, true, false, [], [13]⟩,
        ⟨98, false, false, [77147], []⟩,
        ⟨474, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 011. -/
def y322TCContextRaw011 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77147], [77147], .contexts []⟩,
    ⟨[77147, 1], [77145], .contexts [
        ⟨471, false, false, [], []⟩
      ]⟩,
    ⟨[77145], [77145], .contexts []⟩,
    ⟨[77145, 11], [77143], .contexts [
        ⟨466, true, false, [], [11]⟩,
        ⟨90, false, false, [77143], []⟩,
        ⟨467, false, false, [], []⟩
      ]⟩,
    ⟨[77143], [77143], .contexts []⟩,
    ⟨[77143, 9], [77141], .contexts [
        ⟨464, false, false, [], []⟩
      ]⟩,
    ⟨[77141], [77141], .contexts []⟩,
    ⟨[77141, 1], [77139], .contexts [
        ⟨459, true, false, [], [1]⟩,
        ⟨18, false, false, [77139], []⟩,
        ⟨460, false, false, [], []⟩
      ]⟩,
    ⟨[77139], [77139], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [77139], .contexts [
        ⟨702, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨703, false, false, [], [1, 11, 9, 1]⟩,
        ⟨704, false, false, [], [1, 11, 9, 1]⟩,
        ⟨474, false, false, [], [1, 11, 9, 1]⟩,
        ⟨474, false, false, [], [1, 11, 9, 1]⟩,
        ⟨705, false, false, [], [11, 9, 1]⟩,
        ⟨706, false, false, [], [11, 9, 1]⟩,
        ⟨470, false, false, [], [11, 9, 1]⟩,
        ⟨470, false, false, [], [11, 9, 1]⟩,
        ⟨707, false, false, [], [9, 1]⟩,
        ⟨708, false, false, [], [9, 1]⟩,
        ⟨467, false, false, [], [9, 1]⟩,
        ⟨467, false, false, [], [9, 1]⟩,
        ⟨709, false, false, [], [1]⟩,
        ⟨710, false, false, [], [1]⟩,
        ⟨463, false, false, [], [1]⟩,
        ⟨463, false, false, [], [1]⟩,
        ⟨711, false, false, [], []⟩,
        ⟨712, false, false, [], []⟩,
        ⟨460, false, false, [], []⟩,
        ⟨460, false, false, [], []⟩
      ]⟩,
    ⟨[77139, 5], [77137], .contexts [
        ⟨456, true, false, [], [5]⟩,
        ⟨49, false, false, [77137], []⟩,
        ⟨457, false, false, [], []⟩
      ]⟩,
    ⟨[77137], [77137], .contexts []⟩,
    ⟨[77137, 3], [77135], .contexts [
        ⟨454, false, false, [], []⟩
      ]⟩,
    ⟨[77135], [77135], .contexts []⟩,
    ⟨[77135, 1], [77133], .contexts [
        ⟨450, false, false, [], []⟩
      ]⟩,
    ⟨[77133], [77133], .contexts []⟩,
    ⟨[77131], [77131], .contexts []⟩,
    ⟨[77129], [77129], .contexts []⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [77129], .contexts [
        ⟨713, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨714, false, false, [], [3, 1, 15, 13]⟩,
        ⟨715, false, false, [], [3, 1, 15, 13]⟩,
        ⟨457, false, false, [], [3, 1, 15, 13]⟩,
        ⟨457, false, false, [], [3, 1, 15, 13]⟩,
        ⟨716, false, false, [], [1, 15, 13]⟩,
        ⟨717, false, false, [], [1, 15, 13]⟩,
        ⟨453, false, false, [], [1, 15, 13]⟩,
        ⟨453, false, false, [], [1, 15, 13]⟩,
        ⟨718, false, false, [], [15, 13]⟩,
        ⟨719, false, false, [], [15, 13]⟩,
        ⟨449, false, false, [], [15, 13]⟩,
        ⟨449, false, false, [], [15, 13]⟩,
        ⟨445, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [77131], [13]⟩,
        ⟨446, false, false, [], [13]⟩,
        ⟨720, false, false, [], [13]⟩,
        ⟨446, false, false, [], [13]⟩,
        ⟨446, false, false, [], [13]⟩,
        ⟨443, false, false, [], []⟩,
        ⟨721, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩
      ]⟩,
    ⟨[77129, 1], [77127], .contexts [
        ⟨439, false, false, [], []⟩
      ]⟩,
    ⟨[77127], [77127], .contexts []⟩,
    ⟨[77127, 11], [77125], .contexts [
        ⟨434, true, false, [], [11]⟩,
        ⟨90, false, false, [77125], []⟩,
        ⟨435, false, false, [], []⟩
      ]⟩,
    ⟨[77125], [77125], .contexts []⟩,
    ⟨[77125, 9], [77123], .contexts [
        ⟨431, true, false, [], [9]⟩,
        ⟨76, false, false, [77123], []⟩,
        ⟨432, false, false, [], []⟩
      ]⟩,
    ⟨[77123], [77123], .contexts []⟩,
    ⟨[77123, 1], [77121], .contexts [
        ⟨429, false, false, [], []⟩
      ]⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [77119], .contexts [
        ⟨722, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨723, false, false, [], [11, 9, 1, 5]⟩,
        ⟨724, false, false, [], [11, 9, 1, 5]⟩,
        ⟨438, false, false, [], [11, 9, 1, 5]⟩,
        ⟨438, false, false, [], [11, 9, 1, 5]⟩,
        ⟨725, false, false, [], [9, 1, 5]⟩,
        ⟨726, false, false, [], [9, 1, 5]⟩,
        ⟨435, false, false, [], [9, 1, 5]⟩,
        ⟨435, false, false, [], [9, 1, 5]⟩,
        ⟨727, false, false, [], [1, 5]⟩,
        ⟨728, false, false, [], [1, 5]⟩,
        ⟨432, false, false, [], [1, 5]⟩,
        ⟨432, false, false, [], [1, 5]⟩,
        ⟨729, false, false, [], [5]⟩,
        ⟨425, false, false, [], [5]⟩,
        ⟨425, false, false, [], [5]⟩,
        ⟨424, true, false, [], [5]⟩,
        ⟨49, false, false, [77119], []⟩,
        ⟨417, false, false, [], []⟩,
        ⟨416, false, false, [], []⟩,
        ⟨417, false, false, [], []⟩,
        ⟨417, false, false, [], []⟩
      ]⟩,
    ⟨[77119, 3], [77117], .contexts [
        ⟨415, true, false, [], [3]⟩,
        ⟨35, false, false, [77117], []⟩,
        ⟨398, false, false, [], []⟩
      ]⟩,
    ⟨[77117, 1], [1, 77117], .contexts [
        ⟨403, false, false, [], []⟩
      ]⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [1, 77111], .contexts [
        ⟨730, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨731, false, false, [], [1, 15, 13, 1]⟩,
        ⟨397, false, false, [], [1, 15, 13, 1]⟩,
        ⟨398, false, false, [], [1, 15, 13, 1]⟩,
        ⟨398, false, false, [], [1, 15, 13, 1]⟩,
        ⟨732, false, false, [], [15, 13, 1]⟩,
        ⟨400, false, false, [], [15, 13, 1]⟩,
        ⟨401, false, false, [], [15, 13, 1]⟩,
        ⟨401, false, false, [], [15, 13, 1]⟩,
        ⟨395, true, false, [1], [15, 13, 1]⟩,
        ⟨3, false, false, [1, 77115], [13, 1]⟩,
        ⟨378, false, false, [1], [13, 1]⟩,
        ⟨383, false, false, [], [13, 1]⟩,
        ⟨384, false, false, [], [13, 1]⟩,
        ⟨385, false, false, [], [13, 1]⟩,
        ⟨375, false, false, [1], [1]⟩,
        ⟨380, false, false, [], [1]⟩,
        ⟨381, false, false, [], [1]⟩,
        ⟨382, false, false, [], [1]⟩,
        ⟨364, false, false, [1], []⟩,
        ⟨348, false, false, [], []⟩,
        ⟨349, false, false, [], []⟩,
        ⟨350, false, false, [], []⟩
      ]⟩,
    ⟨[33], [19, 21], .source 81⟩,
    ⟨[19], [1], .source 74⟩,
    ⟨[21], [3], .source 75⟩,
    ⟨[33], [1, 3], .contexts [
        ⟨734, false, false, [], []⟩,
        ⟨735, false, false, [], [21]⟩,
        ⟨736, false, false, [1], []⟩
      ]⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [33, 77105], .contexts [
        ⟨733, false, false, [], [11, 9, 1, 5]⟩,
        ⟨328, true, false, [1], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [1, 77109], [9, 1, 5]⟩,
        ⟨299, false, false, [1], [9, 1, 5]⟩,
        ⟨311, false, false, [], [9, 1, 5]⟩,
        ⟨312, false, false, [], [9, 1, 5]⟩,
        ⟨313, false, false, [], [9, 1, 5]⟩,
        ⟨296, false, false, [1], [1, 5]⟩,
        ⟨279, false, false, [], [1, 5]⟩,
        ⟨280, false, false, [], [1, 5]⟩,
        ⟨281, false, false, [], [1, 5]⟩,
        ⟨259, false, false, [1], [5]⟩,
        ⟨737, true, false, [], [77107, 5]⟩,
        ⟨251, false, false, [33], []⟩
      ]⟩,
    ⟨[35], [33, 31], .source 82⟩,
    ⟨[31], [13], .source 80⟩,
    ⟨[37], [35, 19], .source 83⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [37, 77099], .contexts [
        ⟨738, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨205, false, false, [33], [1, 15, 13, 1]⟩,
        ⟨157, false, false, [33], [15, 13, 1]⟩,
        ⟨154, false, false, [33], [13, 1]⟩,
        ⟨740, true, false, [33], [77101, 13, 1]⟩,
        ⟨739, true, false, [], [77101, 13, 1]⟩,
        ⟨99, false, false, [35], [1]⟩,
        ⟨26, false, false, [35], []⟩,
        ⟨735, true, false, [35], [77099]⟩,
        ⟨741, true, false, [], [77099]⟩
      ]⟩,
    ⟨[39], [37, 29], .source 84⟩,
    ⟨[29], [11], .source 79⟩,
    ⟨[41], [39, 27], .source 85⟩,
    ⟨[27], [9], .source 78⟩,
    ⟨[43], [41, 19], .source 86⟩,
    ⟨[45], [43, 23], .source 87⟩,
    ⟨[23], [5], .source 76⟩,
    ⟨[47], [45, 21], .source 88⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [47, 77099], .contexts [
        ⟨742, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨95, false, false, [37], [9, 1, 5, 3]⟩,
        ⟨744, true, false, [37], [77099, 9, 1, 5, 3]⟩,
        ⟨743, true, false, [], [77099, 9, 1, 5, 3]⟩,
        ⟨81, false, false, [39], [1, 5, 3]⟩,
        ⟨746, true, false, [39], [77099, 1, 5, 3]⟩,
        ⟨745, true, false, [], [77099, 1, 5, 3]⟩,
        ⟨26, false, false, [41], [5, 3]⟩,
        ⟨735, true, false, [41], [77099, 5, 3]⟩,
        ⟨747, true, false, [], [77099, 5, 3]⟩,
        ⟨54, false, false, [43], [3]⟩,
        ⟨749, true, false, [43], [77099, 3]⟩,
        ⟨748, true, false, [], [77099, 3]⟩,
        ⟨40, false, false, [45], []⟩,
        ⟨736, true, false, [45], [77099]⟩,
        ⟨750, true, false, [], [77099]⟩
      ]⟩,
    ⟨[49], [47, 19], .source 89⟩,
    ⟨[51], [49, 31], .source 90⟩,
    ⟨[53], [51, 19], .source 91⟩,
    ⟨[55], [53, 29], .source 92⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [55], .contexts [
        ⟨751, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨26, false, false, [47], [15, 13, 1, 11]⟩,
        ⟨735, true, false, [47], [77099, 15, 13, 1, 11]⟩,
        ⟨752, true, false, [], [77099, 15, 13, 1, 11]⟩,
        ⟨5, false, false, [49], [13, 1, 11]⟩,
        ⟨740, true, false, [49], [1, 11]⟩,
        ⟨753, true, false, [], [1, 11]⟩,
        ⟨735, true, false, [51], [11]⟩,
        ⟨754, true, false, [], [11]⟩,
        ⟨744, true, false, [53], []⟩,
        ⟨755, true, false, [], []⟩
      ]⟩,
    ⟨[57], [55, 27], .source 93⟩,
    ⟨[59], [57, 19], .source 94⟩,
    ⟨[61], [59, 23], .source 95⟩,
    ⟨[63], [61, 21], .source 96⟩,
    ⟨[65], [63, 19], .source 97⟩,
    ⟨[
      77229, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [65], .contexts [
        ⟨756, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨746, true, false, [55], [1, 5, 3, 1]⟩,
        ⟨757, true, false, [], [1, 5, 3, 1]⟩,
        ⟨735, true, false, [57], [5, 3, 1]⟩,
        ⟨758, true, false, [], [5, 3, 1]⟩,
        ⟨749, true, false, [59], [3, 1]⟩,
        ⟨759, true, false, [], [3, 1]⟩,
        ⟨736, true, false, [61], [1]⟩,
        ⟨760, true, false, [], [1]⟩,
        ⟨735, true, false, [63], []⟩,
        ⟨761, true, false, [], []⟩
      ]⟩,
    ⟨[67], [65, 29], .source 98⟩,
    ⟨[
      1, 3, 5, 1, 9, 11, 1, 13, 15, 1, 3, 5,
      1, 9, 11, 1, 13, 15, 1, 3, 5, 1, 9, 11,
      1, 13, 15, 1, 3, 5, 1, 9, 11, 1, 13, 15,
      1, 3, 5, 1, 9, 11, 1, 13, 15, 1, 3, 5,
      1, 9, 11, 1, 13, 15, 1, 3, 5, 1, 9, 11,
      1, 13, 15, 1, 3, 5, 1, 9, 11, 1, 13, 15,
      1, 3, 5, 1, 9, 11, 1, 13, 15, 1, 3, 5,
      1, 9, 11, 1, 13, 15
    ], [], .source 72⟩,
    ⟨[1, 9], [
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10
    ], .contexts [
        ⟨764, false, false, [4, 2, 0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10
        ]⟩
      ]⟩,
    ⟨[4, 2], [5, 3], .contexts [
        ⟨50, false, false, [], [2]⟩,
        ⟨36, false, false, [5], []⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨766, false, false, [], [
          0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
          0
        ]⟩,
        ⟨19, false, false, [5, 3], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [5, 3, 1], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [5, 3, 1, 15], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [5, 3, 1, 15, 13], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [5, 3, 1, 15, 13, 1], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [5, 3, 1, 15, 13, 1, 11], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [5, 3, 1, 15, 13, 1, 11, 9], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [5, 3, 1, 15, 13, 1, 11, 9, 1], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3], [14, 12, 0]⟩,
        ⟨20, false, false, [5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1], [12, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 012. -/
def y322TCContextRaw012 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨767, false, false, [], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11
        ], [0]⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨768, false, false, [], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5
        ], [0]⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨769, false, false, [], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨770, false, false, [], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11
        ], [0]⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨771, false, false, [], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5
        ], [0]⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨772, false, false, [], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0]⟩,
        ⟨20, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0]⟩,
        ⟨108, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩,
    ⟨[
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10
    ], [
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11
    ], .contexts [
        ⟨773, false, false, [], [10]⟩,
        ⟨19, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10]⟩,
        ⟨91, false, false, [
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], []⟩
      ]⟩,
    ⟨[77231, 9], [77231, 9], .contexts []⟩,
    ⟨[77231, 9], [67, 77103], .contexts [
        ⟨775, false, false, [], []⟩,
        ⟨623, true, false, [], [9]⟩,
        ⟨623, true, false, [], [9]⟩,
        ⟨621, true, false, [], [9]⟩,
        ⟨765, false, false, [77229], []⟩,
        ⟨774, false, false, [77229], []⟩,
        ⟨762, false, false, [], [15, 13, 1, 11]⟩,
        ⟨2, false, false, [65], [13, 1, 11]⟩,
        ⟨97, false, false, [65], [1, 11]⟩,
        ⟨156, false, false, [65], [11]⟩,
        ⟨184, false, false, [65], []⟩,
        ⟨744, true, false, [65], [77103]⟩,
        ⟨763, true, false, [], [77103]⟩,
        ⟨167, false, false, [67], []⟩
      ]⟩,
    ⟨[77231, 9], [67, 77103], .contexts [
        ⟨776, false, false, [], []⟩,
        ⟨24, true, false, [], [67, 77103]⟩
      ]⟩,
    ⟨[69], [66], .source 99⟩,
    ⟨[77103, 9], [69, 77231], .contexts [
        ⟨777, true, false, [66], [9]⟩,
        ⟨76, false, false, [66, 77231], []⟩,
        ⟨778, true, false, [], [77231]⟩
      ]⟩,
    ⟨[67, 77103], [67, 77103], .contexts []⟩,
    ⟨[71], [67, 27], .source 100⟩,
    ⟨[71, 77103], [71, 77103], .contexts []⟩,
    ⟨[71, 77103], [71, 77103], .contexts []⟩,
    ⟨[1, 9, 1, 9, 1, 9], [], .source 12⟩,
    ⟨[1, 9, 1, 9, 1, 9], [], .contexts [
        ⟨784, false, false, [], []⟩
      ]⟩,
    ⟨[1, 9], [8, 0, 8, 0], .contexts [
        ⟨785, false, false, [], [8, 0, 8, 0]⟩
      ]⟩,
    ⟨[8, 0], [9, 1], .contexts [
        ⟨77, false, false, [], [0]⟩,
        ⟨19, false, false, [9], []⟩
      ]⟩,
    ⟨[8, 0, 8, 0], [9, 1, 9, 1], .contexts [
        ⟨787, false, false, [], [8, 0]⟩,
        ⟨77, false, false, [9, 1], [0]⟩,
        ⟨19, false, false, [9, 1, 9], []⟩
      ]⟩,
    ⟨[77229, 9], [77229, 9], .contexts []⟩,
    ⟨[77229, 9], [71, 77103], .contexts [
        ⟨789, false, false, [], []⟩,
        ⟨622, true, false, [], [9]⟩,
        ⟨622, true, false, [], [9]⟩,
        ⟨622, true, false, [], [9]⟩,
        ⟨18, true, false, [77229], [9]⟩,
        ⟨621, false, false, [], [1, 9]⟩,
        ⟨786, false, false, [77231], []⟩,
        ⟨788, false, false, [77231], []⟩,
        ⟨775, false, false, [], [1, 9, 1]⟩,
        ⟨777, false, false, [], [1, 9, 1]⟩,
        ⟨780, false, false, [], [1, 9, 1]⟩,
        ⟨780, false, false, [], [1, 9, 1]⟩,
        ⟨157, false, false, [67], [9, 1]⟩,
        ⟨132, false, false, [67], [1]⟩,
        ⟨746, true, false, [67], [77101, 1]⟩,
        ⟨781, true, false, [], [77101, 1]⟩,
        ⟨156, false, false, [71], []⟩,
        ⟨782, false, false, [], []⟩,
        ⟨783, false, false, [], []⟩,
        ⟨167, false, false, [71], []⟩
      ]⟩,
    ⟨[77229, 9], [71, 77103], .contexts [
        ⟨790, false, false, [], []⟩,
        ⟨24, true, false, [], [71, 77103]⟩
      ]⟩,
    ⟨[73], [70], .source 101⟩,
    ⟨[77103, 9], [69, 77231], .contexts [
        ⟨779, false, false, [], []⟩
      ]⟩,
    ⟨[69, 77231], [69, 77231], .contexts []⟩,
    ⟨[75], [67, 73], .source 102⟩,
    ⟨[77], [71, 23], .source 103⟩,
    ⟨[77231], [75, 77229], .contexts [
        ⟨794, true, false, [68], []⟩,
        ⟨794, true, false, [68], []⟩,
        ⟨793, true, false, [68], []⟩,
        ⟨791, true, false, [68, 70], [9]⟩,
        ⟨76, false, false, [68, 70, 77229], []⟩,
        ⟨792, true, false, [68], [77229]⟩,
        ⟨778, false, true, [], [73, 77229]⟩,
        ⟨795, true, false, [], [77229]⟩
      ]⟩,
    ⟨[79], [69, 75], .source 104⟩,
    ⟨[81], [77, 79], .source 105⟩,
    ⟨[81, 77227], [81, 77227], .contexts []⟩,
    ⟨[5, 9, 5, 9], [], .source 28⟩,
    ⟨[9, 5, 9, 5], [], .contexts [
        ⟨801, false, false, [4], [5]⟩
      ]⟩,
    ⟨[81], [81], .contexts []⟩,
    ⟨[77229], [81, 77227], .contexts [
        ⟨802, true, false, [77229], []⟩,
        ⟨789, false, false, [], [5, 9, 5]⟩,
        ⟨791, false, false, [], [5, 9, 5]⟩,
        ⟨782, false, false, [], [5, 9, 5]⟩,
        ⟨783, false, false, [], [5, 9, 5]⟩,
        ⟨783, false, false, [], [5, 9, 5]⟩,
        ⟨168, false, false, [71], [9, 5]⟩,
        ⟨749, true, false, [71], [77103, 9, 5]⟩,
        ⟨796, true, false, [], [77103, 9, 5]⟩,
        ⟨779, false, false, [77], [5]⟩,
        ⟨797, false, false, [77, 69], [5]⟩,
        ⟨798, true, false, [77], [77229, 5]⟩,
        ⟨799, true, false, [], [77229, 5]⟩,
        ⟨619, false, false, [81], []⟩,
        ⟨800, false, false, [], []⟩,
        ⟨803, true, false, [], [77227]⟩
      ]⟩,
    ⟨[83], [75, 81], .source 106⟩,
    ⟨[77231], [83, 77227], .contexts [
        ⟨797, false, false, [], []⟩,
        ⟨804, false, false, [75], []⟩,
        ⟨805, true, false, [], [77227]⟩
      ]⟩,
    ⟨[85], [80], .source 107⟩,
    ⟨[87], [85, 83], .source 108⟩,
    ⟨[77227, 1], [87, 77227], .contexts [
        ⟨804, true, false, [80], [1]⟩,
        ⟨621, false, false, [80], []⟩,
        ⟨806, false, false, [80], []⟩,
        ⟨807, true, false, [], [83, 77227]⟩,
        ⟨808, true, false, [], [77227]⟩
      ]⟩,
    ⟨[89], [85, 71], .source 109⟩,
    ⟨[77227, 9], [89, 77103], .contexts [
        ⟨804, true, false, [80], [9]⟩,
        ⟨791, false, false, [80], []⟩,
        ⟨782, false, false, [80], []⟩,
        ⟨807, true, false, [], [71, 77103]⟩,
        ⟨810, true, false, [], [77103]⟩
      ]⟩,
    ⟨[89, 77103], [89, 77103], .contexts []⟩,
    ⟨[77227, 9], [89, 77103], .contexts [
        ⟨811, false, false, [], []⟩,
        ⟨812, false, false, [], []⟩,
        ⟨812, false, false, [], []⟩
      ]⟩,
    ⟨[91], [89, 25], .source 110⟩,
    ⟨[25], [7], .source 77⟩,
    ⟨[93], [69, 83], .source 111⟩,
    ⟨[95], [91, 93], .source 112⟩,
    ⟨[7, 9, 7, 9], [], .source 36⟩,
    ⟨[9, 7, 9, 7], [], .contexts [
        ⟨818, false, false, [6], [7]⟩
      ]⟩,
    ⟨[9, 7, 9, 7], [], .contexts [
        ⟨819, false, false, [], []⟩
      ]⟩,
    ⟨[77227], [77227], .contexts []⟩,
    ⟨[77227, 7], [77227, 7], .contexts []⟩,
    ⟨[77227], [77227], .contexts []⟩,
    ⟨[97], [94], .source 113⟩,
    ⟨[94], [94], .contexts []⟩,
    ⟨[99], [89, 19], .source 114⟩,
    ⟨[101], [99, 93], .source 115⟩,
    ⟨[9, 13, 9, 13], [], .contexts [
        ⟨314, false, false, [], []⟩
      ]⟩,
    ⟨[77227, 13], [77227, 13], .contexts []⟩,
    ⟨[103], [100], .source 116⟩,
    ⟨[100], [100], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 013. -/
def y322TCContextRaw013 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77227, 13], [103, 77227], .contexts [
        ⟨829, false, false, [], []⟩,
        ⟨827, false, false, [100], [77227, 13]⟩,
        ⟨816, false, false, [100, 99], [77227, 13]⟩,
        ⟨806, true, false, [100, 99, 69], [13]⟩,
        ⟨779, true, false, [100, 99], [13]⟩,
        ⟨826, false, false, [100], [77103, 9, 13]⟩,
        ⟨735, false, false, [100, 89], [77103, 9, 13]⟩,
        ⟨195, true, false, [100, 89], [9, 13]⟩,
        ⟨813, true, false, [100], [13, 9, 13]⟩,
        ⟨828, false, false, [100, 77227], []⟩,
        ⟨821, false, false, [100], []⟩,
        ⟨823, false, false, [100], []⟩,
        ⟨831, true, false, [], [77227]⟩,
        ⟨831, true, false, [], [77227]⟩,
        ⟨830, true, false, [], [77227]⟩
      ]⟩,
    ⟨[105], [89, 31], .source 117⟩,
    ⟨[107], [105, 93], .source 118⟩,
    ⟨[9, 15, 9, 15], [], .contexts [
        ⟨322, false, false, [], []⟩
      ]⟩,
    ⟨[77227, 15], [77227, 15], .contexts []⟩,
    ⟨[109], [106], .source 119⟩,
    ⟨[109], [109], .contexts []⟩,
    ⟨[106], [106], .contexts []⟩,
    ⟨[77227, 15], [109, 77227], .contexts [
        ⟨836, false, false, [], []⟩,
        ⟨834, false, false, [106], [77227, 15]⟩,
        ⟨816, false, false, [106, 105], [77227, 15]⟩,
        ⟨806, true, false, [106, 105, 69], [15]⟩,
        ⟨779, true, false, [106, 105], [15]⟩,
        ⟨833, false, false, [106], [77103, 9, 15]⟩,
        ⟨740, false, false, [106, 89], [77103, 9, 15]⟩,
        ⟨202, true, false, [106, 89], [9, 15]⟩,
        ⟨813, true, false, [106], [15, 9, 15]⟩,
        ⟨835, false, false, [106, 77227], []⟩,
        ⟨821, false, false, [106], []⟩,
        ⟨823, false, false, [106], []⟩,
        ⟨839, true, false, [], [77227]⟩,
        ⟨839, true, false, [], [77227]⟩,
        ⟨837, true, false, [], [77227]⟩,
        ⟨838, true, false, [], [77227]⟩
      ]⟩,
    ⟨[9, 3, 9], [2], .contexts [
        ⟨305, false, false, [], [2]⟩
      ]⟩,
    ⟨[77225, 9], [77225, 9], .contexts []⟩,
    ⟨[111], [92], .source 120⟩,
    ⟨[92], [92], .contexts []⟩,
    ⟨[77225, 9], [111, 77105], .contexts [
        ⟨842, false, false, [], []⟩,
        ⟨615, true, false, [], [9]⟩,
        ⟨816, false, false, [92], [77227, 3, 9]⟩,
        ⟨806, true, false, [92, 69], [3, 9]⟩,
        ⟨793, true, false, [92], [3, 9]⟩,
        ⟨841, false, false, [92, 77103], []⟩,
        ⟨36, false, false, [92, 77103], []⟩,
        ⟨208, false, false, [92], []⟩,
        ⟨218, false, false, [92], []⟩,
        ⟨844, true, false, [], [77105]⟩,
        ⟨844, true, false, [], [77105]⟩,
        ⟨843, true, false, [], [77105]⟩
      ]⟩,
    ⟨[93], [110], .contexts [
        ⟨843, true, true, [], []⟩
      ]⟩,
    ⟨[77105, 9], [93, 77225], .contexts [
        ⟨845, true, false, [110], [9]⟩,
        ⟨76, false, false, [110, 77225], []⟩,
        ⟨846, true, false, [], [77225]⟩
      ]⟩,
    ⟨[87, 77227], [87, 77227], .contexts []⟩,
    ⟨[77227, 1], [87, 77227], .contexts [
        ⟨809, false, false, [], []⟩,
        ⟨848, false, false, [], []⟩,
        ⟨848, false, false, [], []⟩
      ]⟩,
    ⟨[77227, 3], [77225], .contexts [
        ⟨625, false, false, [], []⟩,
        ⟨626, false, false, [], []⟩,
        ⟨614, false, false, [], []⟩,
        ⟨614, false, false, [], []⟩
      ]⟩,
    ⟨[1, 3, 1, 3, 1, 3], [], .contexts [
        ⟨211, false, false, [], []⟩
      ]⟩,
    ⟨[1, 3, 1, 3], [2, 0], .contexts [
        ⟨851, false, false, [], [2, 0]⟩
      ]⟩,
    ⟨[2, 0], [3, 1], .contexts [
        ⟨36, false, false, [], [0]⟩,
        ⟨19, false, false, [3], []⟩
      ]⟩,
    ⟨[77223, 3], [77223, 3], .contexts []⟩,
    ⟨[77223], [77223], .contexts []⟩,
    ⟨[113], [86], .source 121⟩,
    ⟨[86], [86], .contexts []⟩,
    ⟨[113], [86], .contexts [
        ⟨856, false, false, [], []⟩,
        ⟨857, false, false, [], []⟩,
        ⟨857, false, false, [], []⟩
      ]⟩,
    ⟨[97, 77227], [97, 77227], .contexts []⟩,
    ⟨[77227, 7], [97, 77227], .contexts [
        ⟨822, false, false, [], []⟩,
        ⟨822, false, false, [], []⟩,
        ⟨817, false, false, [94], [77227, 7]⟩,
        ⟨816, false, false, [94, 91], [77227, 7]⟩,
        ⟨806, true, false, [94, 91, 69], [7]⟩,
        ⟨779, true, false, [94, 91], [7]⟩,
        ⟨814, false, false, [94], [77103, 9, 7]⟩,
        ⟨815, false, false, [94, 89], [77103, 9, 7]⟩,
        ⟨176, true, false, [94, 89], [9, 7]⟩,
        ⟨813, true, false, [94], [7, 9, 7]⟩,
        ⟨820, false, false, [94, 77227], []⟩,
        ⟨821, false, false, [94], []⟩,
        ⟨823, false, false, [94], []⟩,
        ⟨825, true, false, [], [77227]⟩,
        ⟨825, true, false, [], [77227]⟩,
        ⟨824, true, false, [], [77227]⟩,
        ⟨859, false, false, [], []⟩,
        ⟨859, false, false, [], []⟩
      ]⟩,
    ⟨[97, 77225], [97, 77225], .contexts []⟩,
    ⟨[97, 77225], [97, 77225], .contexts []⟩,
    ⟨[77225, 7], [77225, 7], .contexts []⟩,
    ⟨[77225], [77225], .contexts []⟩,
    ⟨[97], [97], .contexts [
        ⟨24, false, false, [], [97]⟩
      ]⟩,
    ⟨[103, 77227], [103, 77227], .contexts []⟩,
    ⟨[77227, 13], [103, 77227], .contexts [
        ⟨829, false, false, [], []⟩,
        ⟨832, false, false, [], []⟩,
        ⟨866, false, false, [], []⟩,
        ⟨866, false, false, [], []⟩
      ]⟩,
    ⟨[103], [103], .contexts [
        ⟨24, false, false, [], [103]⟩
      ]⟩,
    ⟨[77225, 13], [103, 77225], .contexts [
        ⟨850, true, false, [], [13]⟩,
        ⟨238, false, false, [77227], []⟩,
        ⟨239, false, false, [77227], []⟩,
        ⟨867, false, false, [], [3]⟩,
        ⟨615, false, false, [103], []⟩,
        ⟨864, false, false, [103], []⟩,
        ⟨868, true, false, [], [77225]⟩
      ]⟩,
    ⟨[109, 77227], [109, 77227], .contexts []⟩,
    ⟨[77227, 15], [109, 77227], .contexts [
        ⟨836, false, false, [], []⟩,
        ⟨840, false, false, [], []⟩,
        ⟨870, false, false, [], []⟩,
        ⟨870, false, false, [], []⟩
      ]⟩,
    ⟨[109, 77225], [109, 77225], .contexts []⟩,
    ⟨[109, 77225], [109, 77225], .contexts []⟩,
    ⟨[77225, 15], [77225, 15], .contexts []⟩,
    ⟨[109], [109], .contexts []⟩,
    ⟨[109], [109], .contexts []⟩,
    ⟨[109], [109], .contexts [
        ⟨24, false, false, [], [109]⟩,
        ⟨875, false, false, [], []⟩,
        ⟨876, false, false, [], []⟩
      ]⟩,
    ⟨[77225, 15], [109, 77225], .contexts [
        ⟨874, false, false, [], []⟩,
        ⟨850, true, false, [], [15]⟩,
        ⟨245, false, false, [77227], []⟩,
        ⟨246, false, false, [77227], []⟩,
        ⟨871, false, false, [], [3]⟩,
        ⟨615, false, false, [109], []⟩,
        ⟨872, false, false, [], []⟩,
        ⟨873, false, false, [], []⟩,
        ⟨864, false, false, [109], []⟩,
        ⟨877, true, false, [], [77225]⟩
      ]⟩,
    ⟨[111, 77105], [111, 77105], .contexts []⟩,
    ⟨[77225, 9], [111, 77105], .contexts [
        ⟨842, false, false, [], []⟩,
        ⟨845, false, false, [], []⟩,
        ⟨879, false, false, [], []⟩,
        ⟨879, false, false, [], []⟩
      ]⟩,
    ⟨[115], [111, 21], .source 122⟩,
    ⟨[117], [115, 93], .source 123⟩,
    ⟨[77225, 1], [77223], .contexts [
        ⟨627, false, false, [], []⟩,
        ⟨628, false, false, [], []⟩,
        ⟨610, false, false, [], []⟩,
        ⟨610, false, false, [], []⟩
      ]⟩,
    ⟨[9, 1, 9, 1, 9, 1], [], .contexts [
        ⟨784, false, false, [0], [1]⟩
      ]⟩,
    ⟨[9, 1, 9, 1, 9], [0], .contexts [
        ⟨884, false, false, [], [0]⟩
      ]⟩,
    ⟨[77225, 0], [77225, 1], .contexts [
        ⟨19, false, false, [77225], []⟩
      ]⟩,
    ⟨[119], [116], .source 124⟩,
    ⟨[116], [116], .contexts []⟩,
    ⟨[77223, 9], [119, 77223], .contexts [
        ⟨611, true, false, [], [9]⟩,
        ⟨882, false, false, [116], [77225, 1, 9]⟩,
        ⟨847, true, false, [116, 115], [1, 9]⟩,
        ⟨881, false, false, [116], [77105, 9, 1, 9]⟩,
        ⟨736, false, false, [116, 111], [77105, 9, 1, 9]⟩,
        ⟨220, true, false, [116, 111], [9, 1, 9]⟩,
        ⟨880, true, false, [116], [1, 9, 1, 9]⟩,
        ⟨885, false, false, [116, 77225], []⟩,
        ⟨886, false, false, [116], []⟩,
        ⟨883, false, false, [116], []⟩,
        ⟨855, false, false, [116], []⟩,
        ⟨888, true, false, [], [77223]⟩,
        ⟨888, true, false, [], [77223]⟩,
        ⟨887, true, false, [], [77223]⟩
      ]⟩,
    ⟨[111, 77109], [111, 77109], .contexts []⟩,
    ⟨[111, 77109], [111, 77109], .contexts []⟩,
    ⟨[9, 5, 9, 5], [], .contexts [
        ⟨802, false, false, [], []⟩
      ]⟩,
    ⟨[77225], [77225], .contexts []⟩,
    ⟨[110], [110], .contexts []⟩,
    ⟨[93], [110], .contexts [
        ⟨846, false, false, [], []⟩,
        ⟨894, false, false, [], []⟩,
        ⟨894, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 014. -/
def y322TCContextRaw014 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77109, 5], [93, 77225], .contexts [
        ⟨891, true, false, [110], [5]⟩,
        ⟨890, true, false, [110], [5]⟩,
        ⟨295, true, false, [], [5]⟩,
        ⟨250, true, false, [], [9, 5]⟩,
        ⟨880, true, false, [110], [5, 9, 5]⟩,
        ⟨892, false, false, [110, 77225], []⟩,
        ⟨893, false, false, [110], []⟩,
        ⟨864, false, false, [110], []⟩,
        ⟨895, true, false, [], [77225]⟩
      ]⟩,
    ⟨[77225, 5], [111, 77109], .contexts [
        ⟨896, true, false, [92], [5]⟩,
        ⟨49, false, false, [92, 77109], []⟩,
        ⟨843, true, false, [], [77109]⟩
      ]⟩,
    ⟨[113, 77223], [113, 77223], .contexts []⟩,
    ⟨[77223, 3], [113, 77223], .contexts [
        ⟨854, false, false, [], []⟩,
        ⟨854, false, false, [], []⟩,
        ⟨611, true, false, [], [3]⟩,
        ⟨615, true, false, [], [1, 3]⟩,
        ⟨849, true, false, [86], [3, 1, 3]⟩,
        ⟨852, false, false, [86, 77227], []⟩,
        ⟨853, false, false, [86, 77227], []⟩,
        ⟨850, false, false, [86], [1]⟩,
        ⟨627, false, false, [86], []⟩,
        ⟨628, false, false, [86], []⟩,
        ⟨610, false, false, [86], []⟩,
        ⟨610, false, false, [86], []⟩,
        ⟨855, false, false, [86], []⟩,
        ⟨858, true, false, [], [77223]⟩,
        ⟨898, false, false, [], []⟩,
        ⟨898, false, false, [], []⟩
      ]⟩,
    ⟨[3, 15, 3], [14], .contexts [
        ⟨244, false, false, [], [14]⟩
      ]⟩,
    ⟨[77221, 3], [77221, 3], .contexts []⟩,
    ⟨[77221], [77221], .contexts []⟩,
    ⟨[112], [112], .contexts []⟩,
    ⟨[77221, 3], [87, 77221], .contexts [
        ⟨901, false, false, [], []⟩,
        ⟨608, true, false, [], [3]⟩,
        ⟨899, true, false, [112], [15, 3]⟩,
        ⟨900, false, false, [112, 77223], []⟩,
        ⟨20, false, false, [112, 77223], []⟩,
        ⟨629, false, false, [112], []⟩,
        ⟨630, false, false, [112], []⟩,
        ⟨607, false, false, [112], []⟩,
        ⟨607, false, false, [112], []⟩,
        ⟨902, false, false, [112], []⟩,
        ⟨903, true, false, [], [77221]⟩,
        ⟨903, true, false, [], [77221]⟩,
        ⟨856, false, true, [], [77221]⟩
      ]⟩,
    ⟨[7, 1, 7, 1], [], .contexts [
        ⟨171, false, false, [0], [1]⟩
      ]⟩,
    ⟨[7, 1, 7], [0], .contexts [
        ⟨905, false, false, [], [0]⟩
      ]⟩,
    ⟨[97, 77223, 7], [77225, 1], .contexts [
        ⟨611, true, false, [97], [7]⟩,
        ⟨862, true, false, [], [1, 7]⟩,
        ⟨862, true, false, [], [1, 7]⟩,
        ⟨861, true, false, [], [1, 7]⟩,
        ⟨865, false, false, [], [77225, 1, 7]⟩,
        ⟨864, true, false, [97], [1, 7]⟩,
        ⟨862, true, false, [], [1, 7]⟩,
        ⟨861, true, false, [], [1, 7]⟩,
        ⟨615, true, false, [97], [1, 7]⟩,
        ⟨860, true, false, [], [3, 1, 7]⟩,
        ⟨226, true, false, [77227], [1, 7]⟩,
        ⟨225, true, false, [77227], [1, 7]⟩,
        ⟨850, false, false, [], [7, 1, 7]⟩,
        ⟨863, true, false, [], [1, 7]⟩,
        ⟨863, true, false, [], [1, 7]⟩,
        ⟨906, false, false, [77225], []⟩,
        ⟨886, false, false, [], []⟩
      ]⟩,
    ⟨[96], [96], .contexts []⟩,
    ⟨[109, 77221], [109, 77221], .contexts []⟩,
    ⟨[109, 77221], [109, 77221], .contexts []⟩,
    ⟨[15, 1, 15, 1], [], .contexts [
        ⟨16, false, false, [], []⟩
      ]⟩,
    ⟨[77221, 1], [77221, 1], .contexts []⟩,
    ⟨[107], [108], .contexts [
        ⟨837, true, true, [], []⟩
      ]⟩,
    ⟨[108], [108], .contexts []⟩,
    ⟨[77221, 1], [107, 77225], .contexts [
        ⟨912, false, false, [], []⟩,
        ⟨910, true, false, [108], [1]⟩,
        ⟨909, true, false, [108], [1]⟩,
        ⟨608, true, false, [], [1]⟩,
        ⟨611, true, false, [], [15, 1]⟩,
        ⟨873, true, false, [108], [1, 15, 1]⟩,
        ⟨873, true, false, [108], [1, 15, 1]⟩,
        ⟨872, true, false, [108], [1, 15, 1]⟩,
        ⟨878, true, false, [108], [1, 15, 1]⟩,
        ⟨874, true, false, [108], [1, 15, 1]⟩,
        ⟨911, false, false, [108, 77225], []⟩,
        ⟨893, false, false, [108], []⟩,
        ⟨864, false, false, [108], []⟩,
        ⟨914, true, false, [], [77225]⟩,
        ⟨914, true, false, [], [77225]⟩,
        ⟨913, true, false, [], [77225]⟩
      ]⟩,
    ⟨[77223], [109, 77221], .contexts [
        ⟨883, true, false, [], []⟩,
        ⟨915, true, false, [106], [1]⟩,
        ⟨18, false, false, [106, 77221], []⟩,
        ⟨837, true, false, [], [77221]⟩,
        ⟨909, false, false, [], []⟩,
        ⟨876, true, false, [], [77221]⟩,
        ⟨875, true, false, [], [77221]⟩,
        ⟨838, true, false, [], [77221]⟩
      ]⟩,
    ⟨[77223], [109, 77221], .contexts [
        ⟨916, false, false, [], []⟩,
        ⟨910, false, false, [], []⟩
      ]⟩,
    ⟨[121], [107, 119], .source 125⟩,
    ⟨[123], [121, 109], .source 126⟩,
    ⟨[77221, 9], [123, 77221], .contexts [
        ⟨916, true, false, [108], [9]⟩,
        ⟨889, false, false, [108], []⟩,
        ⟨917, false, false, [108, 119], []⟩,
        ⟨913, true, false, [], [119, 109, 77221]⟩,
        ⟨918, true, false, [], [109, 77221]⟩,
        ⟨919, true, false, [], [77221]⟩
      ]⟩,
    ⟨[125], [107, 95], .source 127⟩,
    ⟨[127], [125, 109], .source 128⟩,
    ⟨[77221, 7], [127, 77221], .contexts [
        ⟨916, true, false, [108], [7]⟩,
        ⟨907, false, false, [108, 96], []⟩,
        ⟨883, false, false, [108, 96], []⟩,
        ⟨855, false, false, [108, 96], []⟩,
        ⟨908, true, false, [108], [77223]⟩,
        ⟨908, true, false, [108], [77223]⟩,
        ⟨824, false, true, [108], [77223]⟩,
        ⟨917, false, false, [108, 95], []⟩,
        ⟨913, true, false, [], [95, 109, 77221]⟩,
        ⟨921, true, false, [], [109, 77221]⟩,
        ⟨922, true, false, [], [77221]⟩
      ]⟩,
    ⟨[123, 77221], [123, 77221], .contexts []⟩,
    ⟨[77221, 13], [77219], .contexts [
        ⟨631, false, false, [], []⟩,
        ⟨632, false, false, [], []⟩,
        ⟨603, false, false, [], []⟩,
        ⟨603, false, false, [], []⟩
      ]⟩,
    ⟨[9, 13, 9], [12], .contexts [
        ⟨314, false, false, [], [12]⟩
      ]⟩,
    ⟨[77221, 12], [77221, 13], .contexts [
        ⟨108, false, false, [77221], []⟩
      ]⟩,
    ⟨[77219], [77219], .contexts []⟩,
    ⟨[129], [122], .source 129⟩,
    ⟨[122], [122], .contexts []⟩,
    ⟨[87, 77221], [87, 77221], .contexts []⟩,
    ⟨[3, 13, 3], [12], .contexts [
        ⟨237, false, false, [], [12]⟩
      ]⟩,
    ⟨[127, 77221], [127, 77221], .contexts []⟩,
    ⟨[7, 13, 7, 13], [], .contexts [
        ⟨122, false, false, [], []⟩
      ]⟩,
    ⟨[7, 13, 7], [12], .contexts [
        ⟨934, false, false, [], [12]⟩
      ]⟩,
    ⟨[131], [126], .source 130⟩,
    ⟨[126], [126], .contexts []⟩,
    ⟨[107, 77225], [107, 77225], .contexts []⟩,
    ⟨[133], [107, 103], .source 131⟩,
    ⟨[135], [133, 109], .source 132⟩,
    ⟨[135, 77217], [135, 77217], .contexts []⟩,
    ⟨[135, 77217], [135, 77217], .contexts []⟩,
    ⟨[77221, 1, 13, 1, 13, 1], [135, 77217], .contexts [
        ⟨912, false, false, [], [13, 1, 13, 1]⟩,
        ⟨915, false, false, [], [13, 1, 13, 1]⟩,
        ⟨938, false, false, [], [13, 1, 13, 1]⟩,
        ⟨938, false, false, [], [13, 1, 13, 1]⟩,
        ⟨869, false, false, [107], [1, 13, 1]⟩,
        ⟨939, true, false, [], [77225, 1, 13, 1]⟩,
        ⟨611, false, false, [133], [13, 1]⟩,
        ⟨917, false, false, [133], [13, 1]⟩,
        ⟨940, true, false, [], [77221, 13, 1]⟩,
        ⟨604, false, false, [135], [1]⟩,
        ⟨601, false, false, [135], []⟩,
        ⟨941, false, false, [], []⟩,
        ⟨942, false, false, [], []⟩
      ]⟩,
    ⟨[1, 13, 1, 13, 1, 13], [], .contexts [
        ⟨188, false, false, [], []⟩
      ]⟩,
    ⟨[137], [134], .source 133⟩,
    ⟨[134], [134], .contexts []⟩,
    ⟨[137], [134], .contexts [
        ⟨945, false, false, [], []⟩,
        ⟨946, false, false, [], []⟩,
        ⟨946, false, false, [], []⟩
      ]⟩,
    ⟨[77217, 13], [137, 77221], .contexts [
        ⟨943, true, false, [134], [13]⟩,
        ⟨944, false, false, [134, 77221], []⟩,
        ⟨902, false, false, [134], []⟩,
        ⟨947, true, false, [], [77221]⟩
      ]⟩,
    ⟨[135], [136], .contexts [
        ⟨945, true, true, [], []⟩
      ]⟩,
    ⟨[135], [135], .contexts []⟩,
    ⟨[135], [135], .contexts []⟩,
    ⟨[135], [135], .contexts []⟩,
    ⟨[77219], [135, 77217], .contexts [
        ⟨925, true, false, [], []⟩,
        ⟨948, true, false, [136], [13]⟩,
        ⟨98, false, false, [136, 77217], []⟩,
        ⟨949, true, false, [], [77217]⟩,
        ⟨941, false, false, [], []⟩,
        ⟨952, true, false, [], [77217]⟩,
        ⟨951, true, false, [], [77217]⟩,
        ⟨950, true, false, [], [77217]⟩
      ]⟩,
    ⟨[77219], [135, 77217], .contexts [
        ⟨953, false, false, [], []⟩,
        ⟨942, false, false, [], []⟩
      ]⟩,
    ⟨[139], [137, 129], .source 134⟩,
    ⟨[141], [139, 135], .source 135⟩,
    ⟨[77217, 9], [141, 77217], .contexts [
        ⟨953, true, false, [134], [9]⟩,
        ⟨604, true, false, [134], [9]⟩,
        ⟨924, true, false, [134, 122], [13, 9]⟩,
        ⟨924, true, false, [134, 122], [13, 9]⟩,
        ⟨920, true, false, [134, 122], [13, 9]⟩,
        ⟨926, false, false, [134, 122, 77221], []⟩,
        ⟨927, false, false, [134, 122], []⟩,
        ⟨925, false, false, [134, 122], []⟩,
        ⟨928, false, false, [134, 122], []⟩,
        ⟨930, true, false, [134], [77219]⟩,
        ⟨930, true, false, [134], [77219]⟩,
        ⟨929, true, false, [134], [77219]⟩,
        ⟨954, false, false, [134, 129], []⟩,
        ⟨945, true, false, [], [129, 135, 77217]⟩,
        ⟨955, true, false, [], [135, 77217]⟩,
        ⟨956, true, false, [], [77217]⟩
      ]⟩,
    ⟨[143], [137, 113], .source 136⟩,
    ⟨[145], [143, 135], .source 137⟩]

/-- Exact literal claimed equations and contextual derivations, block 015. -/
def y322TCContextRaw015 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77217, 3], [145, 77217], .contexts [
        ⟨953, true, false, [134], [3]⟩,
        ⟨604, true, false, [134], [3]⟩,
        ⟨931, true, false, [134, 86], [13, 3]⟩,
        ⟨931, true, false, [134, 86], [13, 3]⟩,
        ⟨904, true, false, [134, 86], [13, 3]⟩,
        ⟨901, true, false, [134, 86], [13, 3]⟩,
        ⟨932, false, false, [134, 86, 77221], []⟩,
        ⟨927, false, false, [134, 86], []⟩,
        ⟨925, false, false, [134, 86], []⟩,
        ⟨928, false, false, [134, 86], []⟩,
        ⟨858, true, false, [134], [77219]⟩,
        ⟨954, false, false, [134, 113], []⟩,
        ⟨945, true, false, [], [113, 135, 77217]⟩,
        ⟨958, true, false, [], [135, 77217]⟩,
        ⟨959, true, false, [], [77217]⟩
      ]⟩,
    ⟨[147], [137, 131], .source 138⟩,
    ⟨[149], [147, 135], .source 139⟩,
    ⟨[141, 77217], [141, 77217], .contexts []⟩,
    ⟨[77217, 11], [77215], .contexts [
        ⟨634, false, false, [], []⟩,
        ⟨635, false, false, [], []⟩,
        ⟨596, false, false, [], []⟩,
        ⟨596, false, false, [], []⟩
      ]⟩,
    ⟨[9, 11, 9, 11, 9, 11], [], .contexts [
        ⟨342, false, false, [], []⟩
      ]⟩,
    ⟨[9, 11, 9, 11], [10, 8], .contexts [
        ⟨965, false, false, [], [10, 8]⟩
      ]⟩,
    ⟨[10, 8], [11, 9], .contexts [
        ⟨91, false, false, [], [8]⟩,
        ⟨77, false, false, [11], []⟩
      ]⟩,
    ⟨[77213, 11], [77213, 11], .contexts []⟩,
    ⟨[77213], [77213], .contexts []⟩,
    ⟨[151], [140], .source 140⟩,
    ⟨[151], [151], .contexts []⟩,
    ⟨[140], [140], .contexts []⟩,
    ⟨[151], [140], .contexts [
        ⟨971, false, false, [], []⟩,
        ⟨970, false, false, [], []⟩,
        ⟨972, false, false, [], []⟩,
        ⟨972, false, false, [], []⟩
      ]⟩,
    ⟨[77213, 11], [151, 77213], .contexts [
        ⟨968, false, false, [], []⟩,
        ⟨593, true, false, [], [11]⟩,
        ⟨597, true, false, [], [9, 11]⟩,
        ⟨963, true, false, [140], [11, 9, 11]⟩,
        ⟨963, true, false, [140], [11, 9, 11]⟩,
        ⟨957, true, false, [140], [11, 9, 11]⟩,
        ⟨966, false, false, [140, 77217], []⟩,
        ⟨967, false, false, [140, 77217], []⟩,
        ⟨964, false, false, [140], [9]⟩,
        ⟨636, false, false, [140], []⟩,
        ⟨637, false, false, [140], []⟩,
        ⟨592, false, false, [140], []⟩,
        ⟨592, false, false, [140], []⟩,
        ⟨969, false, false, [140], []⟩,
        ⟨973, true, false, [], [77213]⟩
      ]⟩,
    ⟨[145, 77217], [145, 77217], .contexts []⟩,
    ⟨[3, 11, 3], [10], .contexts [
        ⟨230, false, false, [], [10]⟩
      ]⟩,
    ⟨[77217, 10], [77217, 11], .contexts [
        ⟨91, false, false, [77217], []⟩
      ]⟩,
    ⟨[77215, 3], [77215, 3], .contexts []⟩,
    ⟨[77215], [77215], .contexts []⟩,
    ⟨[153], [144], .source 141⟩,
    ⟨[144], [144], .contexts []⟩,
    ⟨[77217, 7], [149, 77217], .contexts [
        ⟨953, true, false, [134], [7]⟩,
        ⟨604, true, false, [134], [7]⟩,
        ⟨933, true, false, [134, 126], [13, 7]⟩,
        ⟨933, true, false, [134, 126], [13, 7]⟩,
        ⟨923, true, false, [134, 126], [13, 7]⟩,
        ⟨935, false, false, [134, 126, 77221], []⟩,
        ⟨927, false, false, [134, 126], []⟩,
        ⟨925, false, false, [134, 126], []⟩,
        ⟨928, false, false, [134, 126], []⟩,
        ⟨937, true, false, [134], [77219]⟩,
        ⟨937, true, false, [134], [77219]⟩,
        ⟨936, true, false, [134], [77219]⟩,
        ⟨954, false, false, [134, 131], []⟩,
        ⟨945, true, false, [], [131, 135, 77217]⟩,
        ⟨961, true, false, [], [135, 77217]⟩,
        ⟨962, true, false, [], [77217]⟩
      ]⟩,
    ⟨[149, 77217], [149, 77217], .contexts []⟩,
    ⟨[7, 11, 7, 11], [], .source 37⟩,
    ⟨[7, 11, 7, 11], [], .contexts [
        ⟨984, false, false, [], []⟩
      ]⟩,
    ⟨[77215, 7], [77215, 7], .contexts []⟩,
    ⟨[155], [148], .source 142⟩,
    ⟨[148], [148], .contexts []⟩,
    ⟨[135, 77215], [135, 77215], .contexts []⟩,
    ⟨[135, 77215], [135, 77215], .contexts []⟩,
    ⟨[11, 1, 11, 1], [], .contexts [
        ⟨179, false, false, [0], [1]⟩
      ]⟩,
    ⟨[11, 1], [0, 10], .contexts [
        ⟨991, false, false, [], [0, 10]⟩
      ]⟩,
    ⟨[0, 10], [1, 11], .contexts [
        ⟨19, false, false, [], [10]⟩,
        ⟨91, false, false, [1], []⟩
      ]⟩,
    ⟨[77215, 1], [77215, 1], .contexts []⟩,
    ⟨[135], [135], .contexts [
        ⟨24, false, false, [], [135]⟩,
        ⟨951, false, false, [], []⟩,
        ⟨952, false, false, [], []⟩
      ]⟩,
    ⟨[77215, 1], [135, 77215], .contexts [
        ⟨994, false, false, [], []⟩,
        ⟨964, true, false, [], [1]⟩,
        ⟨992, false, false, [77217], []⟩,
        ⟨993, false, false, [77217], []⟩,
        ⟨599, false, false, [], [11]⟩,
        ⟨954, false, false, [], [11]⟩,
        ⟨942, false, false, [], [11]⟩,
        ⟨942, false, false, [], [11]⟩,
        ⟨597, false, false, [135], []⟩,
        ⟨989, false, false, [], []⟩,
        ⟨990, false, false, [], []⟩,
        ⟨979, false, false, [135], []⟩,
        ⟨995, true, false, [], [77215]⟩
      ]⟩,
    ⟨[151, 77213], [151, 77213], .contexts []⟩,
    ⟨[77213, 11], [151, 77213], .contexts [
        ⟨968, false, false, [], []⟩,
        ⟨974, false, false, [], []⟩,
        ⟨997, false, false, [], []⟩,
        ⟨997, false, false, [], []⟩
      ]⟩,
    ⟨[77213, 1], [77211], .contexts [
        ⟨638, false, false, [], []⟩,
        ⟨639, false, false, [], []⟩,
        ⟨588, false, false, [], []⟩,
        ⟨588, false, false, [], []⟩
      ]⟩,
    ⟨[11, 1, 11], [0], .contexts [
        ⟨991, false, false, [], [0]⟩
      ]⟩,
    ⟨[77211, 11], [77211, 11], .contexts []⟩,
    ⟨[77211], [77211], .contexts []⟩,
    ⟨[150], [150], .contexts []⟩,
    ⟨[141], [150], .contexts [
        ⟨970, true, true, [], []⟩,
        ⟨1003, false, false, [], []⟩,
        ⟨1003, false, false, [], []⟩
      ]⟩,
    ⟨[77211, 11], [141, 77211], .contexts [
        ⟨1001, false, false, [], []⟩,
        ⟨589, true, false, [], [11]⟩,
        ⟨998, true, false, [150], [1, 11]⟩,
        ⟨1000, false, false, [150, 77213], []⟩,
        ⟨19, false, false, [150, 77213], []⟩,
        ⟨999, false, false, [150], []⟩,
        ⟨1002, false, false, [150], []⟩,
        ⟨1004, true, false, [], [77211]⟩
      ]⟩,
    ⟨[153, 77215], [153, 77215], .contexts []⟩,
    ⟨[77215, 3], [153, 77215], .contexts [
        ⟨978, false, false, [], []⟩,
        ⟨978, false, false, [], []⟩,
        ⟨597, true, false, [], [3]⟩,
        ⟨975, true, false, [144], [11, 3]⟩,
        ⟨975, true, false, [144], [11, 3]⟩,
        ⟨960, true, false, [144], [11, 3]⟩,
        ⟨976, false, false, [144, 77217], []⟩,
        ⟨977, false, false, [144], []⟩,
        ⟨964, false, false, [144], []⟩,
        ⟨979, false, false, [144], []⟩,
        ⟨981, true, false, [], [77215]⟩,
        ⟨981, true, false, [], [77215]⟩,
        ⟨980, true, false, [], [77215]⟩,
        ⟨1006, false, false, [], []⟩,
        ⟨1006, false, false, [], []⟩
      ]⟩,
    ⟨[77215, 9], [77213], .contexts [
        ⟨636, false, false, [], []⟩,
        ⟨637, false, false, [], []⟩,
        ⟨592, false, false, [], []⟩,
        ⟨592, false, false, [], []⟩
      ]⟩,
    ⟨[3, 9, 3, 9], [], .contexts [
        ⟨304, false, false, [], []⟩
      ]⟩,
    ⟨[3, 9, 3], [8], .contexts [
        ⟨1009, false, false, [], [8]⟩
      ]⟩,
    ⟨[77215, 8], [77215, 9], .contexts [
        ⟨77, false, false, [77215], []⟩
      ]⟩,
    ⟨[77213, 3], [77213, 3], .contexts []⟩,
    ⟨[152], [152], .contexts []⟩,
    ⟨[77213, 3], [145, 77213], .contexts [
        ⟨1012, false, false, [], []⟩,
        ⟨593, true, false, [], [3]⟩,
        ⟨1007, true, false, [152], [9, 3]⟩,
        ⟨1010, false, false, [152, 77215], []⟩,
        ⟨1011, false, false, [152], []⟩,
        ⟨1008, false, false, [152], []⟩,
        ⟨969, false, false, [152], []⟩,
        ⟨1013, true, false, [], [77213]⟩,
        ⟨1013, true, false, [], [77213]⟩,
        ⟨980, false, true, [], [77213]⟩
      ]⟩,
    ⟨[155, 77215], [155, 77215], .contexts []⟩,
    ⟨[77215, 7], [155, 77215], .contexts [
        ⟨986, false, false, [], []⟩,
        ⟨986, false, false, [], []⟩,
        ⟨597, true, false, [], [7]⟩,
        ⟨983, true, false, [148], [11, 7]⟩,
        ⟨983, true, false, [148], [11, 7]⟩,
        ⟨982, true, false, [148], [11, 7]⟩,
        ⟨985, false, false, [148, 77217], [10]⟩,
        ⟨977, false, false, [148], []⟩,
        ⟨964, false, false, [148], []⟩,
        ⟨979, false, false, [148], []⟩,
        ⟨988, true, false, [], [77215]⟩,
        ⟨988, true, false, [], [77215]⟩,
        ⟨987, true, false, [], [77215]⟩,
        ⟨1015, false, false, [], []⟩,
        ⟨1015, false, false, [], []⟩
      ]⟩,
    ⟨[7, 9, 7, 9], [], .contexts [
        ⟨818, false, false, [], []⟩
      ]⟩,
    ⟨[7, 9, 7], [8], .contexts [
        ⟨1017, false, false, [], [8]⟩
      ]⟩,
    ⟨[77213, 7], [77213, 7], .contexts []⟩,
    ⟨[154], [154], .contexts []⟩,
    ⟨[77215, 1], [135, 77215], .contexts [
        ⟨994, false, false, [], []⟩,
        ⟨996, false, false, [], []⟩,
        ⟨989, false, false, [], []⟩,
        ⟨990, false, false, [], []⟩,
        ⟨990, false, false, [], []⟩
      ]⟩,
    ⟨[1, 9, 1, 9], [8, 0], .contexts [
        ⟨785, false, false, [], [8, 0]⟩
      ]⟩,
    ⟨[77211, 9], [77211, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 016. -/
def y322TCContextRaw016 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77211, 9], [137, 77211], .contexts [
        ⟨1023, false, false, [], []⟩,
        ⟨589, true, false, [], [9]⟩,
        ⟨593, true, false, [], [1, 9]⟩,
        ⟨1021, true, false, [134], [9, 1, 9]⟩,
        ⟨1022, false, false, [134, 77215], []⟩,
        ⟨787, false, false, [134, 77215], []⟩,
        ⟨1008, false, false, [134], [1]⟩,
        ⟨638, false, false, [134], []⟩,
        ⟨639, false, false, [134], []⟩,
        ⟨588, false, false, [134], []⟩,
        ⟨588, false, false, [134], []⟩,
        ⟨1002, false, false, [134], []⟩,
        ⟨947, true, false, [], [77211]⟩
      ]⟩,
    ⟨[141, 77211], [141, 77211], .contexts []⟩,
    ⟨[77211, 5], [77209], .contexts [
        ⟨640, false, false, [], []⟩,
        ⟨641, false, false, [], []⟩,
        ⟨584, false, false, [], []⟩,
        ⟨584, false, false, [], []⟩
      ]⟩,
    ⟨[11, 5, 11, 5], [], .contexts [
        ⟨273, false, false, [4], [5]⟩
      ]⟩,
    ⟨[11, 5, 11], [4], .contexts [
        ⟨1027, false, false, [], [4]⟩
      ]⟩,
    ⟨[77211, 4], [77211, 5], .contexts [
        ⟨50, false, false, [77211], []⟩
      ]⟩,
    ⟨[77209, 11], [77209, 11], .contexts []⟩,
    ⟨[77209], [77209], .contexts []⟩,
    ⟨[149, 77213], [149, 77213], .contexts []⟩,
    ⟨[137, 77211], [137, 77211], .contexts []⟩,
    ⟨[9, 5, 9], [4], .contexts [
        ⟨802, false, false, [], [4]⟩
      ]⟩,
    ⟨[77209, 9], [77209, 9], .contexts []⟩,
    ⟨[136], [136], .contexts []⟩,
    ⟨[151, 77209], [151, 77209], .contexts []⟩,
    ⟨[77209, 11], [151, 77209], .contexts [
        ⟨1030, false, false, [], []⟩,
        ⟨1030, false, false, [], []⟩,
        ⟨585, true, false, [], [11]⟩,
        ⟨1025, true, false, [140], [5, 11]⟩,
        ⟨1025, true, false, [140], [5, 11]⟩,
        ⟨1005, true, false, [140], [5, 11]⟩,
        ⟨1001, true, false, [140], [5, 11]⟩,
        ⟨1028, false, false, [140, 77211], []⟩,
        ⟨1029, false, false, [140], []⟩,
        ⟨1026, false, false, [140], []⟩,
        ⟨1031, false, false, [140], []⟩,
        ⟨973, true, false, [], [77209]⟩,
        ⟨1037, false, false, [], []⟩,
        ⟨1037, false, false, [], []⟩
      ]⟩,
    ⟨[77209, 3], [77207], .contexts [
        ⟨643, false, false, [], []⟩,
        ⟨644, false, false, [], []⟩,
        ⟨580, false, false, [], []⟩,
        ⟨580, false, false, [], []⟩
      ]⟩,
    ⟨[11, 3, 11], [2], .contexts [
        ⟨334, false, false, [], [2]⟩
      ]⟩,
    ⟨[77209, 2], [77209, 3], .contexts [
        ⟨36, false, false, [77209], []⟩
      ]⟩,
    ⟨[77207, 11], [77207, 11], .contexts []⟩,
    ⟨[77207], [77207], .contexts []⟩,
    ⟨[135, 77209], [135, 77209], .contexts []⟩,
    ⟨[77209, 9], [135, 77209], .contexts [
        ⟨1035, false, false, [], []⟩,
        ⟨1035, false, false, [], []⟩,
        ⟨585, true, false, [], [9]⟩,
        ⟨1033, true, false, [136], [5, 9]⟩,
        ⟨1033, true, false, [136], [5, 9]⟩,
        ⟨1024, true, false, [136], [5, 9]⟩,
        ⟨1023, true, false, [136], [5, 9]⟩,
        ⟨1034, false, false, [136, 77211], []⟩,
        ⟨1029, false, false, [136], []⟩,
        ⟨1026, false, false, [136], []⟩,
        ⟨1031, false, false, [136], []⟩,
        ⟨1036, true, false, [], [77209]⟩,
        ⟨1036, true, false, [], [77209]⟩,
        ⟨949, true, false, [], [77209]⟩,
        ⟨950, true, false, [], [77209]⟩,
        ⟨1044, false, false, [], []⟩,
        ⟨1044, false, false, [], []⟩
      ]⟩,
    ⟨[77207, 9], [77207, 9], .contexts []⟩,
    ⟨[141, 77207], [141, 77207], .contexts []⟩,
    ⟨[77207, 11, 1], [141, 77205], .contexts [
        ⟨1042, false, false, [], [1]⟩,
        ⟨1042, false, false, [], [1]⟩,
        ⟨581, true, false, [], [11, 1]⟩,
        ⟨1038, true, false, [150], [3, 11, 1]⟩,
        ⟨1040, false, false, [150, 77209], [1]⟩,
        ⟨1041, false, false, [150], [1]⟩,
        ⟨1039, false, false, [150], [1]⟩,
        ⟨1043, false, false, [150], [1]⟩,
        ⟨1004, true, false, [], [77207, 1]⟩,
        ⟨1047, false, false, [], [1]⟩,
        ⟨1047, false, false, [], [1]⟩,
        ⟨578, false, false, [141], []⟩
      ]⟩,
    ⟨[77205, 11], [77205, 11], .contexts []⟩,
    ⟨[77205], [77205], .contexts []⟩,
    ⟨[77205, 11], [151, 77205], .contexts [
        ⟨1049, false, false, [], []⟩,
        ⟨1048, true, false, [140], [11]⟩,
        ⟨1000, false, false, [140, 77207], []⟩,
        ⟨19, false, false, [140, 77207], []⟩,
        ⟨645, false, false, [140], []⟩,
        ⟨646, false, false, [140], []⟩,
        ⟨577, false, false, [140], []⟩,
        ⟨577, false, false, [140], []⟩,
        ⟨1050, false, false, [140], []⟩,
        ⟨973, true, false, [], [77205]⟩
      ]⟩,
    ⟨[151, 77205], [151, 77205], .contexts []⟩,
    ⟨[77205, 11], [151, 77205], .contexts [
        ⟨1049, false, false, [], []⟩,
        ⟨1051, false, false, [], []⟩,
        ⟨1052, false, false, [], []⟩,
        ⟨1052, false, false, [], []⟩
      ]⟩,
    ⟨[11, 15, 11], [14], .contexts [
        ⟨357, false, false, [], [14]⟩
      ]⟩,
    ⟨[77203, 11], [77203, 11], .contexts []⟩,
    ⟨[77203], [77203], .contexts []⟩,
    ⟨[141, 77203], [141, 77203], .contexts []⟩,
    ⟨[77203, 11, 13], [141, 77201], .contexts [
        ⟨1055, false, false, [], [13]⟩,
        ⟨1055, false, false, [], [13]⟩,
        ⟨574, true, false, [], [11, 13]⟩,
        ⟨1053, true, false, [150], [15, 11, 13]⟩,
        ⟨1054, false, false, [150, 77205], [13]⟩,
        ⟨20, false, false, [150, 77205], [13]⟩,
        ⟨647, false, false, [150], [13]⟩,
        ⟨648, false, false, [150], [13]⟩,
        ⟨573, false, false, [150], [13]⟩,
        ⟨573, false, false, [150], [13]⟩,
        ⟨1056, false, false, [150], [13]⟩,
        ⟨1004, true, false, [], [77203, 13]⟩,
        ⟨1057, false, false, [], [13]⟩,
        ⟨1057, false, false, [], [13]⟩,
        ⟨570, false, false, [141], []⟩
      ]⟩,
    ⟨[77203, 13], [77201], .contexts [
        ⟨649, false, false, [], []⟩,
        ⟨650, false, false, [], []⟩,
        ⟨569, false, false, [], []⟩,
        ⟨569, false, false, [], []⟩
      ]⟩,
    ⟨[11, 13, 11], [12], .contexts [
        ⟨351, false, false, [], [12]⟩
      ]⟩,
    ⟨[77203, 12], [77203, 13], .contexts [
        ⟨108, false, false, [77203], []⟩
      ]⟩,
    ⟨[77201, 11], [77201, 11], .contexts []⟩,
    ⟨[77201], [77201], .contexts []⟩,
    ⟨[151, 77201], [151, 77201], .contexts []⟩,
    ⟨[151, 77197], [151, 77197], .contexts []⟩,
    ⟨[151, 77197], [151, 77197], .contexts []⟩,
    ⟨[77201, 11, 1, 11], [151, 77197], .contexts [
        ⟨1062, false, false, [], [1, 11]⟩,
        ⟨1062, false, false, [], [1, 11]⟩,
        ⟨1058, true, false, [140], [11, 1, 11]⟩,
        ⟨1060, false, false, [140, 77203], [1, 11]⟩,
        ⟨1061, false, false, [140], [1, 11]⟩,
        ⟨1059, false, false, [140], [1, 11]⟩,
        ⟨1063, false, false, [140], [1, 11]⟩,
        ⟨973, true, false, [], [77201, 1, 11]⟩,
        ⟨1064, false, false, [], [1, 11]⟩,
        ⟨1064, false, false, [], [1, 11]⟩,
        ⟨566, false, false, [151], [11]⟩,
        ⟨563, false, false, [151], []⟩,
        ⟨1065, false, false, [], []⟩,
        ⟨1066, false, false, [], []⟩
      ]⟩,
    ⟨[11, 1, 11, 1], [], .contexts [
        ⟨991, false, false, [], []⟩
      ]⟩,
    ⟨[77201, 1], [77199], .contexts [
        ⟨651, false, false, [], []⟩
      ]⟩,
    ⟨[151], [151], .contexts []⟩,
    ⟨[151], [151], .contexts []⟩,
    ⟨[77233], [77227, 11], .source 38681⟩,
    ⟨[77227, 11], [77233], .contexts [
        ⟨1072, true, false, [], []⟩
      ]⟩,
    ⟨[77233, 11], [77227], .contexts [
        ⟨1073, true, false, [], [11]⟩,
        ⟨90, false, false, [77227], []⟩,
        ⟨618, false, false, [], []⟩
      ]⟩,
    ⟨[77233], [77233], .contexts []⟩,
    ⟨[77233], [77233], .contexts []⟩,
    ⟨[77227, 11], [77233], .contexts [
        ⟨1073, false, false, [], []⟩,
        ⟨1075, false, false, [], []⟩,
        ⟨1076, false, false, [], []⟩,
        ⟨1076, false, false, [], []⟩
      ]⟩,
    ⟨[87, 77233], [87, 77233], .contexts []⟩,
    ⟨[87, 77233], [87, 77233], .contexts []⟩,
    ⟨[77233], [77233], .contexts []⟩,
    ⟨[87], [87], .contexts [
        ⟨24, false, false, [], [87]⟩
      ]⟩,
    ⟨[77233, 1], [87, 77233], .contexts [
        ⟨1077, true, false, [], [1]⟩,
        ⟨992, false, false, [77227], []⟩,
        ⟨993, false, false, [77227], []⟩,
        ⟨849, false, false, [], [11]⟩,
        ⟨1073, false, false, [87], []⟩,
        ⟨1078, false, false, [], []⟩,
        ⟨1079, false, false, [], []⟩,
        ⟨1080, false, false, [87], []⟩,
        ⟨1081, true, false, [], [77233]⟩
      ]⟩,
    ⟨[11, 5], [4, 10], .contexts [
        ⟨1027, false, false, [], [4, 10]⟩
      ]⟩,
    ⟨[4, 10], [5, 11], .contexts [
        ⟨50, false, false, [], [10]⟩,
        ⟨91, false, false, [5], []⟩
      ]⟩,
    ⟨[97, 77233], [97, 77233], .contexts []⟩,
    ⟨[97, 77233], [97, 77233], .contexts []⟩,
    ⟨[11, 7, 11, 7], [], .contexts [
        ⟨984, false, false, [6], [7]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 017. -/
def y322TCContextRaw017 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[11, 7], [6, 10], .contexts [
        ⟨1087, false, false, [], [6, 10]⟩
      ]⟩,
    ⟨[6, 10], [7, 11], .contexts [
        ⟨63, false, false, [], [10]⟩,
        ⟨91, false, false, [7], []⟩
      ]⟩,
    ⟨[77233, 7], [77233, 7], .contexts []⟩,
    ⟨[157], [89, 29], .source 143⟩,
    ⟨[159], [157, 93], .source 144⟩,
    ⟨[159, 77233], [159, 77233], .contexts []⟩,
    ⟨[159, 77233], [159, 77233], .contexts []⟩,
    ⟨[77233, 9], [77233, 9], .contexts []⟩,
    ⟨[159], [159], .contexts [
        ⟨24, false, false, [], [159]⟩
      ]⟩,
    ⟨[77233, 9], [159, 77233], .contexts [
        ⟨1095, false, false, [], []⟩,
        ⟨1077, true, false, [], [9]⟩,
        ⟨344, false, false, [77227], []⟩,
        ⟨346, false, false, [77227], []⟩,
        ⟨813, false, false, [], [11, 9, 11]⟩,
        ⟨184, false, false, [89], [9, 11]⟩,
        ⟨744, true, false, [89], [77103, 9, 11]⟩,
        ⟨1091, true, false, [], [77103, 9, 11]⟩,
        ⟨779, false, false, [157], [11]⟩,
        ⟨806, false, false, [157, 69], [11]⟩,
        ⟨816, true, false, [157], [77227, 11]⟩,
        ⟨1092, true, false, [], [77227, 11]⟩,
        ⟨1073, false, false, [159], []⟩,
        ⟨1093, false, false, [], []⟩,
        ⟨1094, false, false, [], []⟩,
        ⟨1080, false, false, [159], []⟩,
        ⟨1096, true, false, [], [77233]⟩
      ]⟩,
    ⟨[109, 77233], [109, 77233], .contexts []⟩,
    ⟨[109, 77233], [109, 77233], .contexts []⟩,
    ⟨[77233, 15], [77233, 15], .contexts []⟩,
    ⟨[77233, 15], [109, 77233], .contexts [
        ⟨1100, false, false, [], []⟩,
        ⟨1077, true, false, [], [15]⟩,
        ⟨358, false, false, [77227], []⟩,
        ⟨359, false, false, [77227], []⟩,
        ⟨871, false, false, [], [11]⟩,
        ⟨1073, false, false, [109], []⟩,
        ⟨1098, false, false, [], []⟩,
        ⟨1099, false, false, [], []⟩,
        ⟨1080, false, false, [109], []⟩,
        ⟨877, true, false, [], [77233]⟩
      ]⟩,
    ⟨[77235], [77233, 3], .source 38682⟩,
    ⟨[77233, 3], [77235], .contexts [
        ⟨1102, true, false, [], []⟩
      ]⟩,
    ⟨[77235, 3], [77233], .contexts [
        ⟨1103, true, false, [], [3]⟩,
        ⟨35, false, false, [77233], []⟩,
        ⟨1076, false, false, [], []⟩
      ]⟩,
    ⟨[77235], [77235], .contexts []⟩,
    ⟨[77233, 3], [77235], .contexts [
        ⟨1103, false, false, [], []⟩,
        ⟨1105, false, false, [], []⟩,
        ⟨1105, false, false, [], []⟩
      ]⟩,
    ⟨[97, 77235], [97, 77235], .contexts []⟩,
    ⟨[97, 77235], [97, 77235], .contexts []⟩,
    ⟨[77235, 7], [77235, 7], .contexts []⟩,
    ⟨[77235, 7], [97, 77235], .contexts [
        ⟨1109, false, false, [], []⟩,
        ⟨1106, true, false, [], [7]⟩,
        ⟨225, false, false, [77233], []⟩,
        ⟨226, false, false, [77233], []⟩,
        ⟨1090, false, false, [], [3]⟩,
        ⟨1090, false, false, [], [3]⟩,
        ⟨1077, true, false, [], [7, 3]⟩,
        ⟨1088, false, false, [77227], [3]⟩,
        ⟨1089, false, false, [77227], [3]⟩,
        ⟨860, false, false, [], [11, 3]⟩,
        ⟨1073, false, false, [97], [3]⟩,
        ⟨1085, false, false, [], [3]⟩,
        ⟨1086, false, false, [], [3]⟩,
        ⟨1080, false, false, [97], [3]⟩,
        ⟨865, true, false, [], [77233, 3]⟩,
        ⟨1085, false, false, [], [3]⟩,
        ⟨1086, false, false, [], [3]⟩,
        ⟨1086, false, false, [], [3]⟩,
        ⟨1103, false, false, [97], []⟩,
        ⟨1107, false, false, [], []⟩,
        ⟨1108, false, false, [], []⟩
      ]⟩,
    ⟨[77235], [77235], .contexts []⟩,
    ⟨[3, 9], [8, 2], .contexts [
        ⟨1009, false, false, [], [8, 2]⟩
      ]⟩,
    ⟨[8, 2], [9, 3], .contexts [
        ⟨77, false, false, [], [2]⟩,
        ⟨36, false, false, [9], []⟩
      ]⟩,
    ⟨[77235, 9], [159, 77235], .contexts [
        ⟨1106, true, false, [], [9]⟩,
        ⟨1112, false, false, [77233], []⟩,
        ⟨1113, false, false, [77233], []⟩,
        ⟨1095, false, false, [], [3]⟩,
        ⟨1097, false, false, [], [3]⟩,
        ⟨1093, false, false, [], [3]⟩,
        ⟨1094, false, false, [], [3]⟩,
        ⟨1094, false, false, [], [3]⟩,
        ⟨1103, false, false, [159], []⟩,
        ⟨1111, false, false, [159], []⟩,
        ⟨1096, true, false, [], [77235]⟩
      ]⟩,
    ⟨[77235, 11], [77235, 11], .contexts []⟩,
    ⟨[], [], .contexts [
        ⟨24, false, false, [], []⟩
      ]⟩,
    ⟨[], [], .contexts [
        ⟨1116, false, false, [], []⟩,
        ⟨23, false, false, [], []⟩
      ]⟩,
    ⟨[], [], .contexts [
        ⟨1117, false, false, [], []⟩,
        ⟨23, false, false, [], []⟩
      ]⟩,
    ⟨[77235, 11], [77225], .contexts [
        ⟨1115, false, false, [], []⟩,
        ⟨1106, true, false, [], [11]⟩,
        ⟨231, false, false, [77233], []⟩,
        ⟨232, false, false, [77233], []⟩,
        ⟨1074, false, false, [], [3]⟩,
        ⟨624, false, false, [], [3]⟩,
        ⟨618, false, false, [], [3]⟩,
        ⟨618, false, false, [], [3]⟩,
        ⟨625, false, false, [], []⟩,
        ⟨626, false, false, [], []⟩,
        ⟨614, false, false, [], []⟩,
        ⟨614, false, false, [], []⟩,
        ⟨864, false, false, [], []⟩,
        ⟨1118, true, false, [], [77225]⟩
      ]⟩,
    ⟨[77225, 11], [77235], .contexts [
        ⟨1119, true, false, [], [11]⟩,
        ⟨90, false, false, [77235], []⟩,
        ⟨1105, false, false, [], []⟩
      ]⟩,
    ⟨[109, 77235], [109, 77235], .contexts []⟩,
    ⟨[109, 77235], [109, 77235], .contexts []⟩,
    ⟨[77235, 15], [77235, 15], .contexts []⟩,
    ⟨[77235, 11], [77225], .contexts [
        ⟨1115, false, false, [], []⟩,
        ⟨1119, false, false, [], []⟩,
        ⟨626, false, false, [], []⟩,
        ⟨614, false, false, [], []⟩,
        ⟨614, false, false, [], []⟩
      ]⟩,
    ⟨[111, 77111], [111, 77111], .contexts []⟩,
    ⟨[111, 77111], [111, 77111], .contexts []⟩,
    ⟨[11, 5, 11, 5], [], .contexts [
        ⟨1027, false, false, [], []⟩
      ]⟩,
    ⟨[77111, 5], [93, 77235], .contexts [
        ⟨1126, true, false, [110], [5]⟩,
        ⟨1125, true, false, [110], [5]⟩,
        ⟨328, true, false, [], [5]⟩,
        ⟨891, true, false, [110], [11, 5]⟩,
        ⟨891, true, false, [110], [11, 5]⟩,
        ⟨890, true, false, [110], [11, 5]⟩,
        ⟨897, true, false, [110], [11, 5]⟩,
        ⟨1124, true, false, [110], [5, 11, 5]⟩,
        ⟨1127, false, false, [110, 77235], []⟩,
        ⟨1111, false, false, [110], []⟩,
        ⟨895, true, false, [], [77235]⟩
      ]⟩,
    ⟨[77235, 5], [111, 77111], .contexts [
        ⟨1128, true, false, [92], [5]⟩,
        ⟨49, false, false, [92, 77111], []⟩,
        ⟨843, true, false, [], [77111]⟩
      ]⟩,
    ⟨[77237], [77113, 9], .source 38683⟩,
    ⟨[77113, 9], [77237], .contexts [
        ⟨1130, true, false, [], []⟩
      ]⟩,
    ⟨[77237, 9], [77113], .contexts [
        ⟨1131, true, false, [], [9]⟩,
        ⟨76, false, false, [77113], []⟩,
        ⟨367, false, false, [], []⟩
      ]⟩,
    ⟨[77113, 9], [77237], .contexts [
        ⟨1131, false, false, [], []⟩
      ]⟩,
    ⟨[77237], [77237], .contexts []⟩,
    ⟨[77237], [77237], .contexts []⟩,
    ⟨[77113, 9], [77237], .contexts [
        ⟨1133, false, false, [], []⟩,
        ⟨1134, false, false, [], []⟩,
        ⟨1135, false, false, [], []⟩,
        ⟨1135, false, false, [], []⟩
      ]⟩,
    ⟨[11, 77113], [11, 77113], .contexts []⟩,
    ⟨[11, 77113], [11, 77113], .contexts []⟩,
    ⟨[11, 77113], [11, 77113], .contexts []⟩,
    ⟨[11, 77237], [11, 77237], .contexts []⟩,
    ⟨[11, 77237], [11, 77237], .contexts []⟩,
    ⟨[11, 77237], [11, 77237], .contexts []⟩,
    ⟨[9, 1], [0, 8, 0, 8], .contexts [
        ⟨884, false, false, [], [0, 8, 0, 8]⟩
      ]⟩,
    ⟨[0, 8], [1, 9], .contexts [
        ⟨19, false, false, [], [8]⟩,
        ⟨77, false, false, [1], []⟩
      ]⟩,
    ⟨[0, 8, 0], [1, 9, 1], .contexts [
        ⟨1144, false, false, [], [0]⟩,
        ⟨19, false, false, [1, 9], []⟩
      ]⟩,
    ⟨[0, 8, 0, 8], [1, 9, 1, 9], .contexts [
        ⟨1145, false, false, [], [8]⟩,
        ⟨77, false, false, [1, 9, 1], []⟩
      ]⟩,
    ⟨[77237, 1], [77237, 1], .contexts []⟩,
    ⟨[77237], [77237], .contexts []⟩,
    ⟨[77237, 1], [11, 77237], .contexts [
        ⟨1147, false, false, [], []⟩,
        ⟨1136, true, false, [], [1]⟩,
        ⟨1143, false, false, [77113], []⟩,
        ⟨1146, false, false, [77113], []⟩,
        ⟨379, false, false, [], [9, 1, 9]⟩,
        ⟨347, false, false, [], [1, 9]⟩,
        ⟨94, true, false, [], [77111, 1, 9]⟩,
        ⟨339, false, false, [], [1, 9]⟩,
        ⟨341, false, false, [], [1, 9]⟩,
        ⟨341, false, false, [], [1, 9]⟩,
        ⟨363, false, false, [11], [9]⟩,
        ⟨1137, false, false, [], [9]⟩,
        ⟨1138, false, false, [], [9]⟩,
        ⟨1139, false, false, [], [9]⟩,
        ⟨1131, false, false, [11], []⟩,
        ⟨1140, false, false, [], []⟩,
        ⟨1141, false, false, [], []⟩,
        ⟨1142, false, false, [], []⟩,
        ⟨1148, false, false, [11], []⟩,
        ⟨94, true, false, [], [77237]⟩
      ]⟩,
    ⟨[77113, 15], [13, 77113], .contexts [
        ⟨370, false, false, [], []⟩,
        ⟨404, false, false, [], []⟩,
        ⟨368, false, false, [], []⟩,
        ⟨369, false, false, [], []⟩,
        ⟨369, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77237], [13, 77237], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 018. -/
def y322TCContextRaw018 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[13, 77237], [13, 77237], .contexts []⟩,
    ⟨[77237, 15], [77237, 15], .contexts []⟩,
    ⟨[77239], [77237, 11], .source 38684⟩,
    ⟨[77237, 11], [77239], .contexts [
        ⟨1154, true, false, [], []⟩
      ]⟩,
    ⟨[77237, 11], [77239], .contexts [
        ⟨1155, false, false, [], []⟩
      ]⟩,
    ⟨[77239], [77239], .contexts []⟩,
    ⟨[77239], [77239], .contexts []⟩,
    ⟨[77237, 11], [77239], .contexts [
        ⟨1156, false, false, [], []⟩,
        ⟨1157, false, false, [], []⟩,
        ⟨1158, false, false, [], []⟩,
        ⟨1158, false, false, [], []⟩
      ]⟩,
    ⟨[77237, 1], [11, 77237], .contexts [
        ⟨1147, false, false, [], []⟩,
        ⟨1149, false, false, [], []⟩,
        ⟨1140, false, false, [], []⟩,
        ⟨1142, false, false, [], []⟩,
        ⟨1142, false, false, [], []⟩
      ]⟩,
    ⟨[11, 77239], [11, 77239], .contexts []⟩,
    ⟨[11, 77239], [11, 77239], .contexts []⟩,
    ⟨[77239], [77239], .contexts []⟩,
    ⟨[77237, 15], [13, 77237], .contexts [
        ⟨1153, false, false, [], []⟩,
        ⟨1153, false, false, [], []⟩,
        ⟨1136, true, false, [], [15]⟩,
        ⟨323, false, false, [77113], []⟩,
        ⟨324, false, false, [77113], []⟩,
        ⟨1150, false, false, [], [9]⟩,
        ⟨1131, false, false, [13], []⟩,
        ⟨1151, false, false, [], []⟩,
        ⟨1152, false, false, [], []⟩,
        ⟨1148, false, false, [13], []⟩,
        ⟨153, true, false, [], [77237]⟩,
        ⟨1151, false, false, [], []⟩,
        ⟨1152, false, false, [], []⟩,
        ⟨1152, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77239], [13, 77239], .contexts []⟩,
    ⟨[13, 77239], [13, 77239], .contexts []⟩,
    ⟨[77241], [77239, 13], .source 38685⟩,
    ⟨[77239, 13], [77241], .contexts [
        ⟨1167, true, false, [], []⟩
      ]⟩,
    ⟨[77241, 13], [77239], .contexts [
        ⟨1168, true, false, [], [13]⟩,
        ⟨98, false, false, [77239], []⟩,
        ⟨1158, false, false, [], []⟩
      ]⟩,
    ⟨[77243], [77241, 15], .source 38686⟩,
    ⟨[77241, 15], [77243], .contexts [
        ⟨1170, true, false, [], []⟩
      ]⟩,
    ⟨[77241], [77241], .contexts []⟩,
    ⟨[77243], [77243], .contexts []⟩,
    ⟨[77243], [77243], .contexts []⟩,
    ⟨[77241, 15], [77243], .contexts [
        ⟨1171, false, false, [], []⟩,
        ⟨1173, false, false, [], []⟩,
        ⟨1174, false, false, [], []⟩,
        ⟨1174, false, false, [], []⟩
      ]⟩,
    ⟨[77241, 13], [77239], .contexts [
        ⟨1169, false, false, [], []⟩
      ]⟩,
    ⟨[77241, 13], [77239], .contexts [
        ⟨1176, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77243], [13, 77243], .contexts []⟩,
    ⟨[77241, 13, 15, 13, 15], [13, 77243], .contexts [
        ⟨1177, false, false, [], [15, 13, 15]⟩,
        ⟨1157, false, false, [], [15, 13, 15]⟩,
        ⟨1158, false, false, [], [15, 13, 15]⟩,
        ⟨1158, false, false, [], [15, 13, 15]⟩,
        ⟨1159, true, false, [], [15, 13, 15]⟩,
        ⟨358, false, false, [77237], [13, 15]⟩,
        ⟨359, false, false, [77237], [13, 15]⟩,
        ⟨1164, false, false, [], [11, 13, 15]⟩,
        ⟨1155, false, false, [13], [13, 15]⟩,
        ⟨1165, false, false, [], [13, 15]⟩,
        ⟨1166, false, false, [], [13, 15]⟩,
        ⟨1163, false, false, [13], [13, 15]⟩,
        ⟨153, true, false, [], [77239, 13, 15]⟩,
        ⟨1165, false, false, [], [13, 15]⟩,
        ⟨1166, false, false, [], [13, 15]⟩,
        ⟨1166, false, false, [], [13, 15]⟩,
        ⟨1168, false, false, [13], [15]⟩,
        ⟨1171, false, false, [13], []⟩,
        ⟨1178, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77243], [13, 77243], .contexts []⟩,
    ⟨[77243], [77243], .contexts []⟩,
    ⟨[77245], [77243, 1], .source 38687⟩,
    ⟨[77243, 1], [77245], .contexts [
        ⟨1182, true, false, [], []⟩
      ]⟩,
    ⟨[77245, 1], [77243], .contexts [
        ⟨1183, true, false, [], [1]⟩,
        ⟨18, false, false, [77243], []⟩,
        ⟨1174, false, false, [], []⟩
      ]⟩,
    ⟨[77247], [77245, 3], .source 38688⟩,
    ⟨[77245, 3], [77247], .contexts [
        ⟨1185, true, false, [], []⟩
      ]⟩,
    ⟨[77245], [77245], .contexts []⟩,
    ⟨[77249], [77247, 5], .source 38689⟩,
    ⟨[77247, 5], [77249], .contexts [
        ⟨1188, true, false, [], []⟩
      ]⟩,
    ⟨[77247], [77247], .contexts []⟩,
    ⟨[77251], [77249, 1], .source 38690⟩,
    ⟨[77249, 1], [77251], .contexts [
        ⟨1191, true, false, [], []⟩
      ]⟩,
    ⟨[77249], [77249], .contexts []⟩,
    ⟨[77253], [77251, 9], .source 38691⟩,
    ⟨[77251, 9], [77253], .contexts [
        ⟨1194, true, false, [], []⟩
      ]⟩,
    ⟨[77251], [77251], .contexts []⟩,
    ⟨[77255], [77253, 11], .source 38692⟩,
    ⟨[77253, 11], [77255], .contexts [
        ⟨1197, true, false, [], []⟩
      ]⟩,
    ⟨[77253], [77253], .contexts []⟩,
    ⟨[77257], [77255, 1], .source 38693⟩,
    ⟨[77255, 1], [77257], .contexts [
        ⟨1200, true, false, [], []⟩
      ]⟩,
    ⟨[77255], [77255], .contexts []⟩,
    ⟨[77259], [77257, 13], .source 38694⟩,
    ⟨[77257, 13], [77259], .contexts [
        ⟨1203, true, false, [], []⟩
      ]⟩,
    ⟨[77257], [77257], .contexts []⟩,
    ⟨[77261], [77259, 15], .source 38695⟩,
    ⟨[77259, 15], [77261], .contexts [
        ⟨1206, true, false, [], []⟩
      ]⟩,
    ⟨[77259], [77259], .contexts []⟩,
    ⟨[77261, 15], [77259], .contexts [
        ⟨1207, true, false, [], [15]⟩,
        ⟨3, false, false, [77259], []⟩,
        ⟨1208, false, false, [], []⟩
      ]⟩,
    ⟨[77263], [77261, 1], .source 38696⟩,
    ⟨[77261, 1], [77263], .contexts [
        ⟨1210, true, false, [], []⟩
      ]⟩,
    ⟨[77261], [77261], .contexts []⟩,
    ⟨[77263, 1], [77261], .contexts [
        ⟨1211, true, false, [], [1]⟩,
        ⟨18, false, false, [77261], []⟩,
        ⟨1212, false, false, [], []⟩
      ]⟩,
    ⟨[77265], [77263, 3], .source 38697⟩,
    ⟨[77263, 3], [77265], .contexts [
        ⟨1214, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 019. -/
def y322TCContextRaw019 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77263], [77263], .contexts []⟩,
    ⟨[77267], [77265, 5], .source 38698⟩,
    ⟨[77265, 5], [77267], .contexts [
        ⟨1217, true, false, [], []⟩
      ]⟩,
    ⟨[77265], [77265], .contexts []⟩,
    ⟨[77267, 5], [77265], .contexts [
        ⟨1218, true, false, [], [5]⟩,
        ⟨49, false, false, [77265], []⟩,
        ⟨1219, false, false, [], []⟩
      ]⟩,
    ⟨[77269], [77267, 1], .source 38699⟩,
    ⟨[77267, 1], [77269], .contexts [
        ⟨1221, true, false, [], []⟩
      ]⟩,
    ⟨[77267], [77267], .contexts []⟩,
    ⟨[77271], [77269, 9], .source 38700⟩,
    ⟨[77269, 9], [77271], .contexts [
        ⟨1224, true, false, [], []⟩
      ]⟩,
    ⟨[77269], [77269], .contexts []⟩,
    ⟨[77271, 9], [77269], .contexts [
        ⟨1225, true, false, [], [9]⟩,
        ⟨76, false, false, [77269], []⟩,
        ⟨1226, false, false, [], []⟩
      ]⟩,
    ⟨[77273], [77271, 11], .source 38701⟩,
    ⟨[77271, 11], [77273], .contexts [
        ⟨1228, true, false, [], []⟩
      ]⟩,
    ⟨[77271], [77271], .contexts []⟩,
    ⟨[77275], [77273, 1], .source 38702⟩,
    ⟨[77273, 1], [77275], .contexts [
        ⟨1231, true, false, [], []⟩
      ]⟩,
    ⟨[77273], [77273], .contexts []⟩,
    ⟨[77275, 1], [77273], .contexts [
        ⟨1232, true, false, [], [1]⟩,
        ⟨18, false, false, [77273], []⟩,
        ⟨1233, false, false, [], []⟩
      ]⟩,
    ⟨[77277], [77275, 13], .source 38703⟩,
    ⟨[77275, 13], [77277], .contexts [
        ⟨1235, true, false, [], []⟩
      ]⟩,
    ⟨[77275], [77275], .contexts []⟩,
    ⟨[77279], [77277, 15], .source 38704⟩,
    ⟨[77277, 15], [77279], .contexts [
        ⟨1238, true, false, [], []⟩
      ]⟩,
    ⟨[77277], [77277], .contexts []⟩,
    ⟨[77281], [77279, 1], .source 38705⟩,
    ⟨[77279, 1], [77281], .contexts [
        ⟨1241, true, false, [], []⟩
      ]⟩,
    ⟨[77279], [77279], .contexts []⟩,
    ⟨[77283], [77281, 3], .source 38706⟩,
    ⟨[77281], [77281], .contexts []⟩,
    ⟨[77285], [77283, 5], .source 38707⟩,
    ⟨[77283], [77283], .contexts []⟩,
    ⟨[77287], [77285, 1], .source 38708⟩,
    ⟨[77285], [77285], .contexts []⟩,
    ⟨[77289], [77287, 9], .source 38709⟩,
    ⟨[77287], [77287], .contexts []⟩,
    ⟨[77291], [77289, 11], .source 38710⟩,
    ⟨[77289], [77289], .contexts []⟩,
    ⟨[77293], [77291, 1], .source 38711⟩,
    ⟨[77291], [77291], .contexts []⟩,
    ⟨[77295], [77293, 13], .source 38712⟩,
    ⟨[77293], [77293], .contexts []⟩,
    ⟨[77297], [77295, 15], .source 38713⟩,
    ⟨[77295], [77295], .contexts []⟩,
    ⟨[77299], [77297, 1], .source 38714⟩,
    ⟨[77297], [77297], .contexts []⟩,
    ⟨[77301], [77299, 3], .source 38715⟩,
    ⟨[77299], [77299], .contexts []⟩,
    ⟨[77303], [77301, 5], .source 38716⟩,
    ⟨[77301], [77301], .contexts []⟩,
    ⟨[77305], [77303, 1], .source 38717⟩,
    ⟨[77303], [77303], .contexts []⟩,
    ⟨[77307], [77305, 9], .source 38718⟩,
    ⟨[77305, 9], [77307], .contexts [
        ⟨1268, true, false, [], []⟩
      ]⟩,
    ⟨[77305], [77305], .contexts []⟩,
    ⟨[77307, 9], [77305], .contexts [
        ⟨1269, true, false, [], [9]⟩,
        ⟨76, false, false, [77305], []⟩,
        ⟨1270, false, false, [], []⟩
      ]⟩,
    ⟨[77309], [77307, 11], .source 38719⟩,
    ⟨[77307], [77307], .contexts []⟩,
    ⟨[77309, 11], [77307], .contexts [
        ⟨1272, false, false, [], [11]⟩,
        ⟨90, false, false, [77307], []⟩,
        ⟨1273, false, false, [], []⟩
      ]⟩,
    ⟨[77311], [77309, 1], .source 38720⟩,
    ⟨[77309, 1], [77311], .contexts [
        ⟨1275, true, false, [], []⟩
      ]⟩,
    ⟨[77309], [77309], .contexts []⟩,
    ⟨[77311, 1], [77309], .contexts [
        ⟨1276, true, false, [], [1]⟩,
        ⟨18, false, false, [77309], []⟩,
        ⟨1277, false, false, [], []⟩
      ]⟩,
    ⟨[77313], [77311, 13], .source 38721⟩]

/-- Exact literal claimed equations and contextual derivations, block 020. -/
def y322TCContextRaw020 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77311], [77311], .contexts []⟩,
    ⟨[77313, 13], [77311], .contexts [
        ⟨1279, false, false, [], [13]⟩,
        ⟨98, false, false, [77311], []⟩,
        ⟨1280, false, false, [], []⟩
      ]⟩,
    ⟨[77315], [77313, 15], .source 38722⟩,
    ⟨[77313], [77313], .contexts []⟩,
    ⟨[77315, 15], [77313], .contexts [
        ⟨1282, false, false, [], [15]⟩,
        ⟨3, false, false, [77313], []⟩,
        ⟨1283, false, false, [], []⟩
      ]⟩,
    ⟨[77317], [77315, 1], .source 38723⟩,
    ⟨[77315, 1], [77317], .contexts [
        ⟨1285, true, false, [], []⟩
      ]⟩,
    ⟨[77315], [77315], .contexts []⟩,
    ⟨[77317, 1], [77315], .contexts [
        ⟨1286, true, false, [], [1]⟩,
        ⟨18, false, false, [77315], []⟩,
        ⟨1287, false, false, [], []⟩
      ]⟩,
    ⟨[77319], [77317, 3], .source 38724⟩,
    ⟨[77317], [77317], .contexts []⟩,
    ⟨[77319, 3], [77317], .contexts [
        ⟨1289, false, false, [], [3]⟩,
        ⟨35, false, false, [77317], []⟩,
        ⟨1290, false, false, [], []⟩
      ]⟩,
    ⟨[77321], [77319, 5], .source 38725⟩,
    ⟨[77319], [77319], .contexts []⟩,
    ⟨[77321, 5], [77319], .contexts [
        ⟨1292, false, false, [], [5]⟩,
        ⟨49, false, false, [77319], []⟩,
        ⟨1293, false, false, [], []⟩
      ]⟩,
    ⟨[77323], [77321, 1], .source 38726⟩,
    ⟨[77321, 1], [77323], .contexts [
        ⟨1295, true, false, [], []⟩
      ]⟩,
    ⟨[77321], [77321], .contexts []⟩,
    ⟨[77323, 1], [77321], .contexts [
        ⟨1296, true, false, [], [1]⟩,
        ⟨18, false, false, [77321], []⟩,
        ⟨1297, false, false, [], []⟩
      ]⟩,
    ⟨[77325], [77323, 9], .source 38727⟩,
    ⟨[77323], [77323], .contexts []⟩,
    ⟨[77325, 9], [77323], .contexts [
        ⟨1299, false, false, [], [9]⟩,
        ⟨76, false, false, [77323], []⟩,
        ⟨1300, false, false, [], []⟩
      ]⟩,
    ⟨[77327], [77325, 11], .source 38728⟩,
    ⟨[77325, 11], [77327], .contexts [
        ⟨1302, true, false, [], []⟩
      ]⟩,
    ⟨[77325], [77325], .contexts []⟩,
    ⟨[77327, 11], [77325], .contexts [
        ⟨1303, true, false, [], [11]⟩,
        ⟨90, false, false, [77325], []⟩,
        ⟨1304, false, false, [], []⟩
      ]⟩,
    ⟨[77329], [77327, 1], .source 38729⟩,
    ⟨[77327, 1], [77329], .contexts [
        ⟨1306, true, false, [], []⟩
      ]⟩,
    ⟨[77327], [77327], .contexts []⟩,
    ⟨[77329, 1], [77327], .contexts [
        ⟨1307, true, false, [], [1]⟩,
        ⟨18, false, false, [77327], []⟩,
        ⟨1308, false, false, [], []⟩
      ]⟩,
    ⟨[77331], [77329, 13], .source 38730⟩,
    ⟨[77329, 13], [77331], .contexts [
        ⟨1310, true, false, [], []⟩
      ]⟩,
    ⟨[77329], [77329], .contexts []⟩,
    ⟨[77331, 13], [77329], .contexts [
        ⟨1311, true, false, [], [13]⟩,
        ⟨98, false, false, [77329], []⟩,
        ⟨1312, false, false, [], []⟩
      ]⟩,
    ⟨[77333], [77331, 15], .source 38731⟩,
    ⟨[77331, 15], [77333], .contexts [
        ⟨1314, true, false, [], []⟩
      ]⟩,
    ⟨[77331], [77331], .contexts []⟩,
    ⟨[77333, 15], [77331], .contexts [
        ⟨1315, true, false, [], [15]⟩,
        ⟨3, false, false, [77331], []⟩,
        ⟨1316, false, false, [], []⟩
      ]⟩,
    ⟨[77335], [77333, 1], .source 38732⟩,
    ⟨[77333, 1], [77335], .contexts [
        ⟨1318, true, false, [], []⟩
      ]⟩,
    ⟨[77333], [77333], .contexts []⟩,
    ⟨[77335, 1], [77333], .contexts [
        ⟨1319, true, false, [], [1]⟩,
        ⟨18, false, false, [77333], []⟩,
        ⟨1320, false, false, [], []⟩
      ]⟩,
    ⟨[77337], [77335, 3], .source 38733⟩,
    ⟨[77335], [77335], .contexts []⟩,
    ⟨[77337, 3], [77335], .contexts [
        ⟨1322, false, false, [], [3]⟩,
        ⟨35, false, false, [77335], []⟩,
        ⟨1323, false, false, [], []⟩
      ]⟩,
    ⟨[77339], [77337, 5], .source 38734⟩,
    ⟨[77337], [77337], .contexts []⟩,
    ⟨[77339, 5], [77337], .contexts [
        ⟨1325, false, false, [], [5]⟩,
        ⟨49, false, false, [77337], []⟩,
        ⟨1326, false, false, [], []⟩
      ]⟩,
    ⟨[77341], [77339, 1], .source 38735⟩,
    ⟨[77339], [77339], .contexts []⟩,
    ⟨[77341, 1], [77339], .contexts [
        ⟨1328, false, false, [], [1]⟩,
        ⟨18, false, false, [77339], []⟩,
        ⟨1329, false, false, [], []⟩
      ]⟩,
    ⟨[77343], [77341, 9], .source 38736⟩,
    ⟨[77341, 9], [77343], .contexts [
        ⟨1331, true, false, [], []⟩
      ]⟩,
    ⟨[77341], [77341], .contexts []⟩,
    ⟨[77343, 9], [77341], .contexts [
        ⟨1332, true, false, [], [9]⟩,
        ⟨76, false, false, [77341], []⟩,
        ⟨1333, false, false, [], []⟩
      ]⟩,
    ⟨[77345], [77343, 11], .source 38737⟩,
    ⟨[77343, 11], [77345], .contexts [
        ⟨1335, true, false, [], []⟩
      ]⟩,
    ⟨[77343], [77343], .contexts []⟩,
    ⟨[77345, 11], [77343], .contexts [
        ⟨1336, true, false, [], [11]⟩,
        ⟨90, false, false, [77343], []⟩,
        ⟨1337, false, false, [], []⟩
      ]⟩,
    ⟨[77347], [77345, 1], .source 38738⟩,
    ⟨[77345, 1], [77347], .contexts [
        ⟨1339, true, false, [], []⟩
      ]⟩,
    ⟨[77345], [77345], .contexts []⟩,
    ⟨[77347, 1], [77345], .contexts [
        ⟨1340, true, false, [], [1]⟩,
        ⟨18, false, false, [77345], []⟩,
        ⟨1341, false, false, [], []⟩
      ]⟩,
    ⟨[77349], [77347, 13], .source 38739⟩]

/-- Exact literal claimed equations and contextual derivations, block 021. -/
def y322TCContextRaw021 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77347, 13], [77349], .contexts [
        ⟨1343, true, false, [], []⟩
      ]⟩,
    ⟨[77347], [77347], .contexts []⟩,
    ⟨[77349, 13], [77347], .contexts [
        ⟨1344, true, false, [], [13]⟩,
        ⟨98, false, false, [77347], []⟩,
        ⟨1345, false, false, [], []⟩
      ]⟩,
    ⟨[77351], [77349, 15], .source 38740⟩,
    ⟨[77349, 15], [77351], .contexts [
        ⟨1347, true, false, [], []⟩
      ]⟩,
    ⟨[77349], [77349], .contexts []⟩,
    ⟨[77351, 15], [77349], .contexts [
        ⟨1348, true, false, [], [15]⟩,
        ⟨3, false, false, [77349], []⟩,
        ⟨1349, false, false, [], []⟩
      ]⟩,
    ⟨[77353], [77351, 1], .source 38741⟩,
    ⟨[77351, 1], [77353], .contexts [
        ⟨1351, true, false, [], []⟩
      ]⟩,
    ⟨[77351], [77351], .contexts []⟩,
    ⟨[77353, 1], [77351], .contexts [
        ⟨1352, true, false, [], [1]⟩,
        ⟨18, false, false, [77351], []⟩,
        ⟨1353, false, false, [], []⟩
      ]⟩,
    ⟨[77355], [77353, 3], .source 38742⟩,
    ⟨[77353, 3], [77355], .contexts [
        ⟨1355, true, false, [], []⟩
      ]⟩,
    ⟨[77353], [77353], .contexts []⟩,
    ⟨[77355, 3], [77353], .contexts [
        ⟨1356, true, false, [], [3]⟩,
        ⟨35, false, false, [77353], []⟩,
        ⟨1357, false, false, [], []⟩
      ]⟩,
    ⟨[77355], [77355], .contexts []⟩,
    ⟨[77353, 1], [77351], .contexts [
        ⟨1354, false, false, [], []⟩,
        ⟨1353, false, false, [], []⟩,
        ⟨1353, false, false, [], []⟩
      ]⟩,
    ⟨[77349], [77349], .contexts []⟩,
    ⟨[77349, 13], [77347], .contexts [
        ⟨1346, false, false, [], []⟩
      ]⟩,
    ⟨[77347], [77347], .contexts []⟩,
    ⟨[77347, 1], [77345], .contexts [
        ⟨1342, false, false, [], []⟩
      ]⟩,
    ⟨[77345], [77345], .contexts []⟩,
    ⟨[77345, 11], [77343], .contexts [
        ⟨1338, false, false, [], []⟩
      ]⟩,
    ⟨[77343], [77343], .contexts []⟩,
    ⟨[77343, 9], [77341], .contexts [
        ⟨1334, false, false, [], []⟩
      ]⟩,
    ⟨[77341], [77341], .contexts []⟩,
    ⟨[77353, 1, 15, 13, 1, 11, 9], [77341], .contexts [
        ⟨1360, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨1350, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1361, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1349, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1349, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1362, false, false, [], [1, 11, 9]⟩,
        ⟨1363, false, false, [], [1, 11, 9]⟩,
        ⟨1345, false, false, [], [1, 11, 9]⟩,
        ⟨1345, false, false, [], [1, 11, 9]⟩,
        ⟨1364, false, false, [], [11, 9]⟩,
        ⟨1365, false, false, [], [11, 9]⟩,
        ⟨1341, false, false, [], [11, 9]⟩,
        ⟨1341, false, false, [], [11, 9]⟩,
        ⟨1366, false, false, [], [9]⟩,
        ⟨1367, false, false, [], [9]⟩,
        ⟨1337, false, false, [], [9]⟩,
        ⟨1337, false, false, [], [9]⟩,
        ⟨1368, false, false, [], []⟩,
        ⟨1369, false, false, [], []⟩,
        ⟨1333, false, false, [], []⟩,
        ⟨1333, false, false, [], []⟩
      ]⟩,
    ⟨[77341, 1], [77339], .contexts [
        ⟨1330, false, false, [], []⟩
      ]⟩,
    ⟨[77339], [77339], .contexts []⟩,
    ⟨[77337, 3], [77335], .contexts [
        ⟨1324, false, false, [], []⟩
      ]⟩,
    ⟨[77335], [77335], .contexts []⟩,
    ⟨[77333, 15], [77331], .contexts [
        ⟨1317, false, false, [], []⟩
      ]⟩,
    ⟨[77331], [77331], .contexts []⟩,
    ⟨[77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [77331], .contexts [
        ⟨1370, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨1371, false, false, [], [5, 3, 1, 15]⟩,
        ⟨1372, false, false, [], [5, 3, 1, 15]⟩,
        ⟨1329, false, false, [], [5, 3, 1, 15]⟩,
        ⟨1329, false, false, [], [5, 3, 1, 15]⟩,
        ⟨1327, false, false, [], [3, 1, 15]⟩,
        ⟨1326, false, false, [], [3, 1, 15]⟩,
        ⟨1326, false, false, [], [3, 1, 15]⟩,
        ⟨1373, false, false, [], [1, 15]⟩,
        ⟨1374, false, false, [], [1, 15]⟩,
        ⟨1323, false, false, [], [1, 15]⟩,
        ⟨1323, false, false, [], [1, 15]⟩,
        ⟨1321, false, false, [], [15]⟩,
        ⟨1320, false, false, [], [15]⟩,
        ⟨1320, false, false, [], [15]⟩,
        ⟨1375, false, false, [], []⟩,
        ⟨1376, false, false, [], []⟩,
        ⟨1316, false, false, [], []⟩,
        ⟨1316, false, false, [], []⟩
      ]⟩,
    ⟨[77331, 13], [77329], .contexts [
        ⟨1313, false, false, [], []⟩
      ]⟩,
    ⟨[77329], [77329], .contexts []⟩,
    ⟨[77329, 1], [77327], .contexts [
        ⟨1309, false, false, [], []⟩
      ]⟩,
    ⟨[77327], [77327], .contexts []⟩,
    ⟨[77327, 11], [77325], .contexts [
        ⟨1305, false, false, [], []⟩
      ]⟩,
    ⟨[77325], [77325], .contexts []⟩,
    ⟨[77325, 9], [77323], .contexts [
        ⟨1301, false, false, [], []⟩
      ]⟩,
    ⟨[77323], [77323], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [77321], .contexts [
        ⟨1377, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨1378, false, false, [], [1, 11, 9, 1]⟩,
        ⟨1379, false, false, [], [1, 11, 9, 1]⟩,
        ⟨1312, false, false, [], [1, 11, 9, 1]⟩,
        ⟨1312, false, false, [], [1, 11, 9, 1]⟩,
        ⟨1380, false, false, [], [11, 9, 1]⟩,
        ⟨1381, false, false, [], [11, 9, 1]⟩,
        ⟨1308, false, false, [], [11, 9, 1]⟩,
        ⟨1308, false, false, [], [11, 9, 1]⟩,
        ⟨1382, false, false, [], [9, 1]⟩,
        ⟨1383, false, false, [], [9, 1]⟩,
        ⟨1304, false, false, [], [9, 1]⟩,
        ⟨1304, false, false, [], [9, 1]⟩,
        ⟨1384, false, false, [], [1]⟩,
        ⟨1385, false, false, [], [1]⟩,
        ⟨1300, false, false, [], [1]⟩,
        ⟨1300, false, false, [], [1]⟩,
        ⟨1298, false, false, [], []⟩,
        ⟨1297, false, false, [], []⟩,
        ⟨1297, false, false, [], []⟩
      ]⟩,
    ⟨[77321, 5], [77319], .contexts [
        ⟨1294, false, false, [], []⟩
      ]⟩,
    ⟨[77319], [77319], .contexts []⟩,
    ⟨[77319, 3], [77317], .contexts [
        ⟨1291, false, false, [], []⟩
      ]⟩,
    ⟨[77317], [77317], .contexts []⟩,
    ⟨[77317, 1], [77315], .contexts [
        ⟨1288, false, false, [], []⟩
      ]⟩,
    ⟨[77315], [77315], .contexts []⟩,
    ⟨[77315, 15], [77313], .contexts [
        ⟨1284, false, false, [], []⟩
      ]⟩,
    ⟨[77313], [77313], .contexts []⟩,
    ⟨[77313, 13], [77311], .contexts [
        ⟨1281, false, false, [], []⟩
      ]⟩,
    ⟨[77311], [77311], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [77311], .contexts [
        ⟨1386, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨1387, false, false, [], [3, 1, 15, 13]⟩,
        ⟨1388, false, false, [], [3, 1, 15, 13]⟩,
        ⟨1293, false, false, [], [3, 1, 15, 13]⟩,
        ⟨1293, false, false, [], [3, 1, 15, 13]⟩,
        ⟨1389, false, false, [], [1, 15, 13]⟩,
        ⟨1390, false, false, [], [1, 15, 13]⟩,
        ⟨1290, false, false, [], [1, 15, 13]⟩,
        ⟨1290, false, false, [], [1, 15, 13]⟩,
        ⟨1391, false, false, [], [15, 13]⟩,
        ⟨1392, false, false, [], [15, 13]⟩,
        ⟨1287, false, false, [], [15, 13]⟩,
        ⟨1287, false, false, [], [15, 13]⟩,
        ⟨1393, false, false, [], [13]⟩,
        ⟨1394, false, false, [], [13]⟩,
        ⟨1283, false, false, [], [13]⟩,
        ⟨1283, false, false, [], [13]⟩,
        ⟨1395, false, false, [], []⟩,
        ⟨1396, false, false, [], []⟩,
        ⟨1280, false, false, [], []⟩,
        ⟨1280, false, false, [], []⟩
      ]⟩,
    ⟨[77307], [77307], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5
    ], [77301], .contexts [
        ⟨1397, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨1278, false, false, [], [11, 9, 1, 5]⟩,
        ⟨1277, false, false, [], [11, 9, 1, 5]⟩,
        ⟨1277, false, false, [], [11, 9, 1, 5]⟩,
        ⟨1274, false, false, [], [9, 1, 5]⟩,
        ⟨1398, false, false, [], [9, 1, 5]⟩,
        ⟨1273, false, false, [], [9, 1, 5]⟩,
        ⟨1273, false, false, [], [9, 1, 5]⟩,
        ⟨1271, false, false, [], [1, 5]⟩,
        ⟨1270, false, false, [], [1, 5]⟩,
        ⟨1270, false, false, [], [1, 5]⟩,
        ⟨1266, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [77303], [5]⟩,
        ⟨1267, false, false, [], [5]⟩,
        ⟨1267, false, false, [], [5]⟩,
        ⟨1267, false, false, [], [5]⟩,
        ⟨1264, false, false, [], [5]⟩,
        ⟨49, false, false, [77301], []⟩,
        ⟨1265, false, false, [], []⟩,
        ⟨1265, false, false, [], []⟩,
        ⟨1265, false, false, [], []⟩
      ]⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13
    ], [77293], .contexts [
        ⟨1399, false, false, [], [3, 1, 15, 13]⟩,
        ⟨1262, false, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [77299], [1, 15, 13]⟩,
        ⟨1263, false, false, [], [1, 15, 13]⟩,
        ⟨1263, false, false, [], [1, 15, 13]⟩,
        ⟨1263, false, false, [], [1, 15, 13]⟩,
        ⟨1260, false, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [77297], [15, 13]⟩,
        ⟨1261, false, false, [], [15, 13]⟩,
        ⟨1261, false, false, [], [15, 13]⟩,
        ⟨1261, false, false, [], [15, 13]⟩,
        ⟨1258, false, false, [], [15, 13]⟩,
        ⟨3, false, false, [77295], [13]⟩,
        ⟨1259, false, false, [], [13]⟩,
        ⟨1259, false, false, [], [13]⟩,
        ⟨1259, false, false, [], [13]⟩,
        ⟨1256, false, false, [], [13]⟩,
        ⟨98, false, false, [77293], []⟩,
        ⟨1257, false, false, [], []⟩,
        ⟨1257, false, false, [], []⟩,
        ⟨1257, false, false, [], []⟩
      ]⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [77285], .contexts [
        ⟨1400, false, false, [], [1, 11, 9, 1]⟩,
        ⟨1254, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [77291], [11, 9, 1]⟩,
        ⟨1255, false, false, [], [11, 9, 1]⟩,
        ⟨1255, false, false, [], [11, 9, 1]⟩,
        ⟨1255, false, false, [], [11, 9, 1]⟩,
        ⟨1252, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [77289], [9, 1]⟩,
        ⟨1253, false, false, [], [9, 1]⟩,
        ⟨1253, false, false, [], [9, 1]⟩,
        ⟨1253, false, false, [], [9, 1]⟩,
        ⟨1250, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [77287], [1]⟩,
        ⟨1251, false, false, [], [1]⟩,
        ⟨1251, false, false, [], [1]⟩,
        ⟨1251, false, false, [], [1]⟩,
        ⟨1248, false, false, [], [1]⟩,
        ⟨18, false, false, [77285], []⟩,
        ⟨1249, false, false, [], []⟩,
        ⟨1249, false, false, [], []⟩,
        ⟨1249, false, false, [], []⟩
      ]⟩,
    ⟨[77279], [77279], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [77277], .contexts [
        ⟨1401, false, false, [], [5, 3, 1, 15]⟩,
        ⟨1246, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [77283], [3, 1, 15]⟩,
        ⟨1247, false, false, [], [3, 1, 15]⟩,
        ⟨1247, false, false, [], [3, 1, 15]⟩,
        ⟨1247, false, false, [], [3, 1, 15]⟩,
        ⟨1244, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [77281], [1, 15]⟩,
        ⟨1245, false, false, [], [1, 15]⟩,
        ⟨1245, false, false, [], [1, 15]⟩,
        ⟨1245, false, false, [], [1, 15]⟩,
        ⟨1242, true, false, [], [1, 15]⟩,
        ⟨18, false, false, [77279], [15]⟩,
        ⟨1243, false, false, [], [15]⟩,
        ⟨1402, false, false, [], [15]⟩,
        ⟨1243, false, false, [], [15]⟩,
        ⟨1243, false, false, [], [15]⟩,
        ⟨1239, true, false, [], [15]⟩,
        ⟨3, false, false, [77277], []⟩,
        ⟨1240, false, false, [], []⟩,
        ⟨1240, false, false, [], []⟩,
        ⟨1240, false, false, [], []⟩
      ]⟩,
    ⟨[77275], [77275], .contexts []⟩,
    ⟨[77273], [77273], .contexts []⟩,
    ⟨[77273, 11], [77271], .contexts [
        ⟨1229, true, false, [], [11]⟩,
        ⟨90, false, false, [77271], []⟩,
        ⟨1230, false, false, [], []⟩
      ]⟩,
    ⟨[77271], [77271], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 022. -/
def y322TCContextRaw022 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77271, 9], [77269], .contexts [
        ⟨1227, false, false, [], []⟩
      ]⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [77269], .contexts [
        ⟨1403, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1236, true, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [77275], [1, 11, 9]⟩,
        ⟨1237, false, false, [], [1, 11, 9]⟩,
        ⟨1404, false, false, [], [1, 11, 9]⟩,
        ⟨1237, false, false, [], [1, 11, 9]⟩,
        ⟨1237, false, false, [], [1, 11, 9]⟩,
        ⟨1234, false, false, [], [11, 9]⟩,
        ⟨1405, false, false, [], [11, 9]⟩,
        ⟨1233, false, false, [], [11, 9]⟩,
        ⟨1233, false, false, [], [11, 9]⟩,
        ⟨1406, false, false, [], [9]⟩,
        ⟨1407, false, false, [], [9]⟩,
        ⟨1230, false, false, [], [9]⟩,
        ⟨1230, false, false, [], [9]⟩,
        ⟨1408, false, false, [], []⟩,
        ⟨1226, false, false, [], []⟩,
        ⟨1226, false, false, [], []⟩
      ]⟩,
    ⟨[77267], [77267], .contexts []⟩,
    ⟨[77267, 5], [77265], .contexts [
        ⟨1220, false, false, [], []⟩
      ]⟩,
    ⟨[77265], [77265], .contexts []⟩,
    ⟨[77265, 3], [77263], .contexts [
        ⟨1215, true, false, [], [3]⟩,
        ⟨35, false, false, [77263], []⟩,
        ⟨1216, false, false, [], []⟩
      ]⟩,
    ⟨[77263], [77263], .contexts []⟩,
    ⟨[77263, 1], [77261], .contexts [
        ⟨1213, false, false, [], []⟩
      ]⟩,
    ⟨[77261], [77261], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [77261], .contexts [
        ⟨1409, false, false, [], [1, 5, 3, 1]⟩,
        ⟨1222, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [77267], [5, 3, 1]⟩,
        ⟨1223, false, false, [], [5, 3, 1]⟩,
        ⟨1410, false, false, [], [5, 3, 1]⟩,
        ⟨1223, false, false, [], [5, 3, 1]⟩,
        ⟨1223, false, false, [], [5, 3, 1]⟩,
        ⟨1411, false, false, [], [3, 1]⟩,
        ⟨1412, false, false, [], [3, 1]⟩,
        ⟨1219, false, false, [], [3, 1]⟩,
        ⟨1219, false, false, [], [3, 1]⟩,
        ⟨1413, false, false, [], [1]⟩,
        ⟨1414, false, false, [], [1]⟩,
        ⟨1216, false, false, [], [1]⟩,
        ⟨1216, false, false, [], [1]⟩,
        ⟨1415, false, false, [], []⟩,
        ⟨1416, false, false, [], []⟩,
        ⟨1212, false, false, [], []⟩,
        ⟨1212, false, false, [], []⟩
      ]⟩,
    ⟨[77259], [77259], .contexts []⟩,
    ⟨[77255], [77255], .contexts []⟩,
    ⟨[77253], [77253], .contexts []⟩,
    ⟨[77251], [77251], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9
    ], [77251], .contexts [
        ⟨1417, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨1209, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1418, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1208, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1208, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1204, true, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [77257], [1, 11, 9]⟩,
        ⟨1205, false, false, [], [1, 11, 9]⟩,
        ⟨1205, false, false, [], [1, 11, 9]⟩,
        ⟨1205, false, false, [], [1, 11, 9]⟩,
        ⟨1201, true, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [77255], [11, 9]⟩,
        ⟨1202, false, false, [], [11, 9]⟩,
        ⟨1419, false, false, [], [11, 9]⟩,
        ⟨1202, false, false, [], [11, 9]⟩,
        ⟨1202, false, false, [], [11, 9]⟩,
        ⟨1198, true, false, [], [11, 9]⟩,
        ⟨90, false, false, [77253], [9]⟩,
        ⟨1199, false, false, [], [9]⟩,
        ⟨1420, false, false, [], [9]⟩,
        ⟨1199, false, false, [], [9]⟩,
        ⟨1199, false, false, [], [9]⟩,
        ⟨1195, true, false, [], [9]⟩,
        ⟨76, false, false, [77251], []⟩,
        ⟨1196, false, false, [], []⟩,
        ⟨1421, false, false, [], []⟩,
        ⟨1196, false, false, [], []⟩,
        ⟨1196, false, false, [], []⟩
      ]⟩,
    ⟨[77249], [77249], .contexts []⟩,
    ⟨[77249, 5], [77247], .contexts [
        ⟨1189, true, false, [], [5]⟩,
        ⟨49, false, false, [77247], []⟩,
        ⟨1190, false, false, [], []⟩
      ]⟩,
    ⟨[77247], [77247], .contexts []⟩,
    ⟨[77245], [77245], .contexts []⟩,
    ⟨[77245, 1], [77243], .contexts [
        ⟨1184, false, false, [], []⟩
      ]⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [77243], .contexts [
        ⟨1422, false, false, [], [1, 5, 3, 1]⟩,
        ⟨1192, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [77249], [5, 3, 1]⟩,
        ⟨1193, false, false, [], [5, 3, 1]⟩,
        ⟨1423, false, false, [], [5, 3, 1]⟩,
        ⟨1193, false, false, [], [5, 3, 1]⟩,
        ⟨1193, false, false, [], [5, 3, 1]⟩,
        ⟨1424, false, false, [], [3, 1]⟩,
        ⟨1425, false, false, [], [3, 1]⟩,
        ⟨1190, false, false, [], [3, 1]⟩,
        ⟨1190, false, false, [], [3, 1]⟩,
        ⟨1186, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [77245], [1]⟩,
        ⟨1187, false, false, [], [1]⟩,
        ⟨1426, false, false, [], [1]⟩,
        ⟨1187, false, false, [], [1]⟩,
        ⟨1187, false, false, [], [1]⟩,
        ⟨1427, false, false, [], []⟩,
        ⟨1173, false, false, [], []⟩,
        ⟨1174, false, false, [], []⟩,
        ⟨1174, false, false, [], []⟩
      ]⟩,
    ⟨[77241], [77241], .contexts []⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [11, 77237], .contexts [
        ⟨1428, false, false, [], [15, 13, 1, 11]⟩,
        ⟨1171, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77241], [13, 1, 11]⟩,
        ⟨1172, false, false, [], [13, 1, 11]⟩,
        ⟨1429, false, false, [], [13, 1, 11]⟩,
        ⟨1172, false, false, [], [13, 1, 11]⟩,
        ⟨1172, false, false, [], [13, 1, 11]⟩,
        ⟨1176, false, false, [], [1, 11]⟩,
        ⟨1157, false, false, [], [1, 11]⟩,
        ⟨1158, false, false, [], [1, 11]⟩,
        ⟨1158, false, false, [], [1, 11]⟩,
        ⟨1159, true, false, [], [1, 11]⟩,
        ⟨992, false, false, [77237], [11]⟩,
        ⟨993, false, false, [77237], [11]⟩,
        ⟨1160, false, false, [], [11, 11]⟩,
        ⟨1155, false, false, [11], [11]⟩,
        ⟨1161, false, false, [], [11]⟩,
        ⟨1162, false, false, [], [11]⟩,
        ⟨1163, false, false, [11], [11]⟩,
        ⟨94, true, false, [], [77239, 11]⟩,
        ⟨1161, false, false, [], [11]⟩,
        ⟨1162, false, false, [], [11]⟩,
        ⟨1162, false, false, [], [11]⟩,
        ⟨1155, true, false, [11], [11]⟩,
        ⟨90, false, false, [11, 77237], []⟩,
        ⟨1135, false, false, [11], []⟩,
        ⟨1140, false, false, [], []⟩,
        ⟨1141, false, false, [], []⟩,
        ⟨1142, false, false, [], []⟩
      ]⟩,
    ⟨[161], [29, 93], .source 145⟩,
    ⟨[163], [161, 87], .source 146⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [163, 77233], .contexts [
        ⟨1430, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨1132, false, false, [11], [1, 5, 3, 1]⟩,
        ⟨1137, false, false, [], [1, 5, 3, 1]⟩,
        ⟨1138, false, false, [], [1, 5, 3, 1]⟩,
        ⟨1139, false, false, [], [1, 5, 3, 1]⟩,
        ⟨364, false, false, [11], [5, 3, 1]⟩,
        ⟨339, false, false, [], [5, 3, 1]⟩,
        ⟨340, false, false, [], [5, 3, 1]⟩,
        ⟨341, false, false, [], [5, 3, 1]⟩,
        ⟨1128, false, false, [11], [3, 1]⟩,
        ⟨744, true, false, [], [93, 77235, 3, 1]⟩,
        ⟨1431, true, false, [], [77235, 3, 1]⟩,
        ⟨1104, false, false, [161], [1]⟩,
        ⟨1082, false, false, [161], []⟩,
        ⟨1432, true, false, [], [77233]⟩
      ]⟩,
    ⟨[165], [163, 109], .source 147⟩,
    ⟨[167], [165, 103], .source 148⟩,
    ⟨[169], [167, 87], .source 149⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [169, 77227], .contexts [
        ⟨1433, false, false, [], [15, 13, 1, 11]⟩,
        ⟨1101, false, false, [163], [13, 1, 11]⟩,
        ⟨1434, true, false, [], [77233, 13, 1, 11]⟩,
        ⟨1077, true, false, [165], [13, 1, 11]⟩,
        ⟨352, false, false, [165, 77227], [1, 11]⟩,
        ⟨353, false, false, [165, 77227], [1, 11]⟩,
        ⟨867, false, false, [165], [11, 1, 11]⟩,
        ⟨1073, false, false, [165, 103], [1, 11]⟩,
        ⟨1080, false, false, [165, 103], [1, 11]⟩,
        ⟨868, true, false, [165], [77233, 1, 11]⟩,
        ⟨1435, true, false, [], [77233, 1, 11]⟩,
        ⟨1082, false, false, [167], [11]⟩,
        ⟨1436, true, false, [], [77233, 11]⟩,
        ⟨1074, false, false, [169], []⟩
      ]⟩,
    ⟨[171], [169, 89], .source 150⟩,
    ⟨[173], [171, 23], .source 151⟩,
    ⟨[175], [173, 21], .source 152⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [175, 77103], .contexts [
        ⟨1437, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨811, false, false, [169], [1, 5, 3, 1]⟩,
        ⟨1438, true, false, [], [77103, 1, 5, 3, 1]⟩,
        ⟨157, false, false, [171], [5, 3, 1]⟩,
        ⟨119, false, false, [171], [3, 1]⟩,
        ⟨749, true, false, [171], [77101, 3, 1]⟩,
        ⟨1439, true, false, [], [77101, 3, 1]⟩,
        ⟨111, false, false, [173], [1]⟩,
        ⟨736, true, false, [173], [77101, 1]⟩,
        ⟨1440, true, false, [], [77101, 1]⟩,
        ⟨156, false, false, [175], []⟩
      ]⟩,
    ⟨[177], [175, 31], .source 153⟩,
    ⟨[179], [177, 19], .source 154⟩,
    ⟨[181], [179, 29], .source 155⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [181, 9, 77101], .contexts [
        ⟨1441, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨202, false, false, [175], [13, 1, 11, 9]⟩,
        ⟨740, true, false, [175], [77103, 13, 1, 11, 9]⟩,
        ⟨1442, true, false, [], [77103, 13, 1, 11, 9]⟩,
        ⟨195, false, false, [177], [1, 11, 9]⟩,
        ⟨735, true, false, [177], [77103, 1, 11, 9]⟩,
        ⟨1443, true, false, [], [77103, 1, 11, 9]⟩,
        ⟨157, false, false, [179], [11, 9]⟩,
        ⟨140, false, false, [179], [9]⟩,
        ⟨744, true, false, [179], [77101, 9]⟩,
        ⟨1444, true, false, [], [77101, 9]⟩,
        ⟨132, false, false, [181], []⟩
      ]⟩,
    ⟨[183], [181, 27], .source 156⟩,
    ⟨[185], [183, 23], .source 157⟩,
    ⟨[187], [185, 21], .source 158⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [187, 77105, 15], .contexts [
        ⟨1445, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨746, true, false, [181], [77101, 1, 5, 3, 1, 15]⟩,
        ⟨1446, true, false, [], [77101, 1, 5, 3, 1, 15]⟩,
        ⟨156, false, false, [183], [5, 3, 1, 15]⟩,
        ⟨168, false, false, [183], [3, 1, 15]⟩,
        ⟨749, true, false, [183], [77103, 3, 1, 15]⟩,
        ⟨1447, true, false, [], [77103, 3, 1, 15]⟩,
        ⟨204, false, false, [185], [1, 15]⟩,
        ⟨220, false, false, [185], [15]⟩,
        ⟨736, true, false, [185], [77105, 15]⟩,
        ⟨1448, true, false, [], [77105, 15]⟩
      ]⟩,
    ⟨[189], [187, 31], .source 159⟩,
    ⟨[191], [189, 19], .source 160⟩,
    ⟨[193], [191, 21], .source 161⟩,
    ⟨[195], [193, 29], .source 162⟩,
    ⟨[197], [195, 93], .source 163⟩,
    ⟨[
      77353, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9
    ], [197, 77225], .contexts [
        ⟨1449, false, false, [], [13, 1, 11, 9]⟩,
        ⟨248, false, false, [187], [13, 1, 11, 9]⟩,
        ⟨740, true, false, [187], [77105, 13, 1, 11, 9]⟩,
        ⟨1450, true, false, [], [77105, 13, 1, 11, 9]⟩,
        ⟨241, false, false, [189], [1, 11, 9]⟩,
        ⟨735, true, false, [189], [77105, 1, 11, 9]⟩,
        ⟨1451, true, false, [], [77105, 1, 11, 9]⟩,
        ⟨220, false, false, [191], [11, 9]⟩,
        ⟨736, true, false, [191], [77105, 11, 9]⟩,
        ⟨1452, true, false, [], [77105, 11, 9]⟩,
        ⟨234, false, false, [193], [9]⟩,
        ⟨744, true, false, [193], [77105, 9]⟩,
        ⟨1453, true, false, [], [77105, 9]⟩,
        ⟨847, false, false, [195], []⟩,
        ⟨1454, true, false, [], [77225]⟩
      ]⟩,
    ⟨[199], [197, 109], .source 164⟩,
    ⟨[3, 5], [
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0
    ], .contexts [
        ⟨764, false, false, [0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0
        ]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨21, false, false, [], [
          12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
          8
        ]⟩,
        ⟨108, false, false, [1, 15], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [1, 15, 13], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [1, 15, 13, 1], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [1, 15, 13, 1, 11], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [1, 15, 13, 1, 11, 9], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [1, 15, 13, 1, 11, 9, 1], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [1, 15, 13, 1, 11, 9, 1, 5], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [1, 15, 13, 1, 11, 9, 1, 5, 3], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [1, 15, 13, 1, 11, 9, 1, 5, 3, 1], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [0, 10, 8]⟩,
        ⟨19, false, false, [1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [10, 8]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨1458, false, false, [], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨1459, false, false, [], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨1460, false, false, [], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨1461, false, false, [], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨1462, false, false, [], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨1463, false, false, [], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8]⟩,
        ⟨91, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0
    ], [
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], .contexts [
        ⟨1464, false, false, [], [0]⟩,
        ⟨77, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0]⟩,
        ⟨19, false, false, [
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], []⟩
      ]⟩,
    ⟨[77355, 5], [77355, 5], .contexts []⟩,
    ⟨[77355, 5], [199, 77221], .contexts [
        ⟨1466, false, false, [], []⟩,
        ⟨1359, true, false, [], [5]⟩,
        ⟨1359, true, false, [], [5]⟩,
        ⟨1356, true, false, [], [5]⟩,
        ⟨1457, false, false, [77353], []⟩,
        ⟨1465, false, false, [77353], []⟩,
        ⟨1455, false, false, [], [1]⟩,
        ⟨611, false, false, [197], []⟩,
        ⟨917, false, false, [197], []⟩,
        ⟨1456, true, false, [], [77221]⟩,
        ⟨902, false, false, [199], []⟩,
        ⟨24, true, false, [], [199, 77221]⟩
      ]⟩,
    ⟨[201], [198], .source 165⟩,
    ⟨[77221, 5], [201, 77355], .contexts [
        ⟨1467, true, false, [198], [5]⟩,
        ⟨49, false, false, [198, 77355], []⟩,
        ⟨1468, true, false, [], [77355]⟩
      ]⟩,
    ⟨[77355, 3], [77353], .contexts [
        ⟨1358, false, false, [], []⟩
      ]⟩,
    ⟨[77355, 3], [77353], .contexts [
        ⟨1470, false, false, [], []⟩,
        ⟨1357, false, false, [], []⟩,
        ⟨1357, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 023. -/
def y322TCContextRaw023 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[199, 77221], [199, 77221], .contexts []⟩,
    ⟨[77355, 5], [199, 77221], .contexts [
        ⟨1466, false, false, [], []⟩,
        ⟨1467, false, false, [], []⟩,
        ⟨1472, false, false, [], []⟩,
        ⟨1472, false, false, [], []⟩
      ]⟩,
    ⟨[203], [199, 87], .source 166⟩,
    ⟨[205], [203, 201], .source 167⟩,
    ⟨[205, 77353], [205, 77353], .contexts []⟩,
    ⟨[205, 77353], [205, 77353], .contexts []⟩,
    ⟨[3, 5, 3, 5, 3, 5], [], .contexts [
        ⟨262, false, false, [], []⟩
      ]⟩,
    ⟨[3, 5], [4, 2, 4, 2], .contexts [
        ⟨1478, false, false, [], [4, 2, 4, 2]⟩
      ]⟩,
    ⟨[4, 2, 4], [5, 3, 5], .contexts [
        ⟨766, false, false, [], [4]⟩,
        ⟨50, false, false, [5, 3], []⟩
      ]⟩,
    ⟨[4, 2, 4, 2], [5, 3, 5, 3], .contexts [
        ⟨1480, false, false, [], [2]⟩,
        ⟨36, false, false, [5, 3, 5], []⟩
      ]⟩,
    ⟨[77353, 5], [77353, 5], .contexts []⟩,
    ⟨[207], [199, 107], .source 168⟩,
    ⟨[209], [207, 111], .source 169⟩,
    ⟨[5, 1, 5, 1], [], .contexts [
        ⟨255, false, false, [], []⟩
      ]⟩,
    ⟨[77355], [77355], .contexts []⟩,
    ⟨[77109, 1], [77109, 1], .contexts []⟩,
    ⟨[77355], [77355], .contexts []⟩,
    ⟨[211], [208], .source 170⟩,
    ⟨[208], [208], .contexts []⟩,
    ⟨[77109, 1], [211, 77355], .contexts [
        ⟨1487, false, false, [], []⟩,
        ⟨1484, false, false, [208], [77109, 1]⟩,
        ⟨897, true, false, [208, 207], [1]⟩,
        ⟨1483, false, false, [208], [77225, 5, 1]⟩,
        ⟨915, true, false, [208, 199], [5, 1]⟩,
        ⟨1473, true, false, [208], [1, 5, 1]⟩,
        ⟨1485, false, false, [208, 77355], []⟩,
        ⟨1486, false, false, [208], []⟩,
        ⟨1488, false, false, [208], []⟩,
        ⟨1490, true, false, [], [77355]⟩,
        ⟨1490, true, false, [], [77355]⟩,
        ⟨1489, true, false, [], [77355]⟩
      ]⟩,
    ⟨[209], [210], .contexts [
        ⟨1489, true, true, [], []⟩
      ]⟩,
    ⟨[77355, 1], [209, 77109], .contexts [
        ⟨1491, true, false, [210], [1]⟩,
        ⟨18, false, false, [210, 77109], []⟩,
        ⟨1492, true, false, [], [77109]⟩
      ]⟩,
    ⟨[213], [199, 123], .source 171⟩,
    ⟨[215], [213, 201], .source 172⟩,
    ⟨[5, 9, 5, 9], [], .contexts [
        ⟨801, false, false, [], []⟩
      ]⟩,
    ⟨[5, 9, 5, 9], [], .contexts [
        ⟨1496, false, false, [], []⟩
      ]⟩,
    ⟨[77355, 9], [77355, 9], .contexts []⟩,
    ⟨[217], [214], .source 173⟩,
    ⟨[214], [214], .contexts []⟩,
    ⟨[77355, 9], [217, 77355], .contexts [
        ⟨1498, false, false, [], []⟩,
        ⟨1495, false, false, [214], [77355, 9]⟩,
        ⟨1469, true, false, [214, 213], [9]⟩,
        ⟨1494, false, false, [214], [77221, 5, 9]⟩,
        ⟨920, true, false, [214, 199], [5, 9]⟩,
        ⟨1473, true, false, [214], [9, 5, 9]⟩,
        ⟨1497, false, false, [214, 77355], []⟩,
        ⟨1486, false, false, [214], []⟩,
        ⟨1488, false, false, [214], []⟩,
        ⟨1500, true, false, [], [77355]⟩,
        ⟨1500, true, false, [], [77355]⟩,
        ⟨1499, true, false, [], [77355]⟩
      ]⟩,
    ⟨[219], [199, 109], .source 174⟩,
    ⟨[221], [219, 201], .source 175⟩,
    ⟨[5, 15, 5, 15], [], .contexts [
        ⟨289, false, false, [], []⟩
      ]⟩,
    ⟨[77355, 15], [77355, 15], .contexts []⟩,
    ⟨[223], [220], .source 176⟩,
    ⟨[220], [220], .contexts []⟩,
    ⟨[77353, 5], [205, 77353], .contexts [
        ⟨1482, false, false, [], []⟩,
        ⟨1482, false, false, [], []⟩,
        ⟨1471, true, false, [], [5]⟩,
        ⟨1479, false, false, [77355], []⟩,
        ⟨1481, false, false, [77355], []⟩,
        ⟨1473, false, false, [], [3, 5, 3]⟩,
        ⟨904, false, false, [199], [5, 3]⟩,
        ⟨1474, true, false, [], [77221, 5, 3]⟩,
        ⟨1469, false, false, [203], [3]⟩,
        ⟨1475, true, false, [], [77355, 3]⟩,
        ⟨1358, false, false, [205], []⟩,
        ⟨1476, false, false, [], []⟩,
        ⟨1477, false, false, [], []⟩,
        ⟨24, true, false, [], [205, 77353]⟩,
        ⟨1476, false, false, [], []⟩,
        ⟨1477, false, false, [], []⟩
      ]⟩,
    ⟨[5, 1, 5], [0], .contexts [
        ⟨255, false, false, [], [0]⟩
      ]⟩,
    ⟨[77351], [77351], .contexts []⟩,
    ⟨[225], [204], .source 177⟩,
    ⟨[204], [204], .contexts []⟩,
    ⟨[211, 77355], [211, 77355], .contexts []⟩,
    ⟨[211, 77355], [211, 77355], .contexts []⟩,
    ⟨[77109, 1], [211, 77355], .contexts [
        ⟨1487, false, false, [], []⟩,
        ⟨1491, false, false, [], []⟩,
        ⟨1513, false, false, [], []⟩,
        ⟨1514, false, false, [], []⟩,
        ⟨1514, false, false, [], []⟩
      ]⟩,
    ⟨[227], [23, 211], .source 178⟩,
    ⟨[209], [210], .contexts [
        ⟨1492, false, false, [], []⟩
      ]⟩,
    ⟨[229], [209, 227], .source 179⟩,
    ⟨[231], [228], .source 180⟩,
    ⟨[77353], [231, 77351], .contexts [
        ⟨1471, true, false, [], []⟩,
        ⟨1518, false, false, [228], [77355, 3]⟩,
        ⟨1517, false, false, [228], [227, 77355, 3]⟩,
        ⟨1488, true, false, [228, 210, 227], [3]⟩,
        ⟨1516, false, false, [228, 210], [77355, 3]⟩,
        ⟨749, false, false, [228, 210], [211, 77355, 3]⟩,
        ⟨1491, true, false, [228, 210, 5], [3]⟩,
        ⟨333, true, false, [228, 210], [1, 3]⟩,
        ⟨853, true, false, [228, 210, 77109], [3]⟩,
        ⟨852, true, false, [228, 210, 77109], [3]⟩,
        ⟨1515, false, false, [228, 210], [3, 1, 3, 3]⟩,
        ⟨1358, false, false, [228], [1, 3, 3]⟩,
        ⟨1354, false, false, [228], [3, 3]⟩,
        ⟨35, false, false, [228, 77351], []⟩,
        ⟨1519, true, false, [], [77351]⟩
      ]⟩,
    ⟨[231, 77351], [231, 77351], .contexts []⟩,
    ⟨[77353], [231, 77351], .contexts [
        ⟨1520, false, false, [], []⟩,
        ⟨1521, false, false, [], []⟩
      ]⟩,
    ⟨[77355, 11], [77355, 11], .contexts []⟩,
    ⟨[210], [210], .contexts []⟩,
    ⟨[77355, 11], [209, 77113], .contexts [
        ⟨1523, false, false, [], []⟩,
        ⟨1515, true, false, [210], [11]⟩,
        ⟨181, false, false, [210, 77109], []⟩,
        ⟨182, false, false, [210, 77109], []⟩,
        ⟨332, false, false, [210], [1]⟩,
        ⟨365, false, false, [210], []⟩,
        ⟨366, false, false, [210], []⟩,
        ⟨367, false, false, [210], []⟩,
        ⟨367, false, false, [210], []⟩,
        ⟨371, false, false, [210], []⟩,
        ⟨1524, true, false, [], [77113]⟩,
        ⟨1524, true, false, [], [77113]⟩,
        ⟨1517, true, false, [], [77113]⟩
      ]⟩,
    ⟨[77113, 11], [211, 77355], .contexts [
        ⟨1525, true, false, [208], [11]⟩,
        ⟨90, false, false, [208, 77355], []⟩,
        ⟨1489, true, false, [], [77355]⟩
      ]⟩,
    ⟨[217, 77355], [217, 77355], .contexts []⟩,
    ⟨[77355, 9], [217, 77355], .contexts [
        ⟨1498, false, false, [], []⟩,
        ⟨1501, false, false, [], []⟩,
        ⟨1527, false, false, [], []⟩,
        ⟨1527, false, false, [], []⟩
      ]⟩,
    ⟨[233], [217, 231], .source 181⟩,
    ⟨[77355, 3], [231, 77351], .contexts [
        ⟨1470, false, false, [], []⟩,
        ⟨1522, false, false, [], []⟩,
        ⟨1521, false, false, [], []⟩,
        ⟨1521, false, false, [], []⟩
      ]⟩,
    ⟨[235], [232], .source 182⟩,
    ⟨[237], [235, 231], .source 183⟩,
    ⟨[239], [217, 209], .source 184⟩,
    ⟨[209, 77113], [209, 77113], .contexts []⟩,
    ⟨[77355, 11], [209, 77113], .contexts [
        ⟨1523, false, false, [], []⟩,
        ⟨1525, false, false, [], []⟩,
        ⟨1534, false, false, [], []⟩,
        ⟨1534, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 024. -/
def y322TCContextRaw024 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[9, 11, 9, 11, 9], [10], .contexts [
        ⟨965, false, false, [], [10]⟩
      ]⟩,
    ⟨[241], [238], .source 185⟩,
    ⟨[243], [241, 209], .source 186⟩,
    ⟨[77239, 9], [243, 77113], .contexts [
        ⟨1155, true, false, [], [9]⟩,
        ⟨1131, true, false, [], [11, 9]⟩,
        ⟨1533, false, false, [238], [77113, 9, 11, 9]⟩,
        ⟨1525, true, false, [238, 217], [9, 11, 9]⟩,
        ⟨1528, true, false, [238], [11, 9, 11, 9]⟩,
        ⟨1536, false, false, [238, 77355], []⟩,
        ⟨91, false, false, [238, 77355], []⟩,
        ⟨1535, false, false, [238], []⟩,
        ⟨371, false, false, [238, 209], []⟩,
        ⟨1537, true, false, [], [209, 77113]⟩,
        ⟨1538, true, false, [], [77113]⟩
      ]⟩,
    ⟨[245], [242], .source 187⟩,
    ⟨[245], [245], .contexts []⟩,
    ⟨[245], [245], .contexts []⟩,
    ⟨[245], [245], .contexts []⟩,
    ⟨[243], [244], .contexts [
        ⟨1540, true, true, [], []⟩
      ]⟩,
    ⟨[77239], [243, 77237], .contexts [
        ⟨1541, false, false, [244], [77239]⟩,
        ⟨1542, false, false, [244], [77239]⟩,
        ⟨1543, false, false, [244], [77239]⟩,
        ⟨1540, false, false, [244], [77239]⟩,
        ⟨76, true, false, [244, 242, 77239], []⟩,
        ⟨1539, false, false, [244, 242], [9]⟩,
        ⟨1136, false, false, [244], []⟩,
        ⟨1544, true, false, [], [77237]⟩
      ]⟩,
    ⟨[243, 77237], [243, 77237], .contexts []⟩,
    ⟨[77239], [243, 77237], .contexts [
        ⟨1545, false, false, [], []⟩,
        ⟨1546, false, false, [], []⟩
      ]⟩,
    ⟨[245], [242], .contexts [
        ⟨1540, false, false, [], []⟩
      ]⟩,
    ⟨[242], [242], .contexts []⟩,
    ⟨[77237, 13], [245, 77241], .contexts [
        ⟨1545, true, false, [242], [13]⟩,
        ⟨1168, false, false, [242], []⟩,
        ⟨1429, false, false, [242], []⟩,
        ⟨1549, true, false, [], [77241]⟩,
        ⟨1549, true, false, [], [77241]⟩,
        ⟨1548, true, false, [], [77241]⟩
      ]⟩,
    ⟨[223, 77355], [223, 77355], .contexts []⟩,
    ⟨[77355, 15], [223, 77355], .contexts [
        ⟨1505, false, false, [], []⟩,
        ⟨1505, false, false, [], []⟩,
        ⟨1503, false, false, [220], [77355, 15]⟩,
        ⟨1469, true, false, [220, 219], [15]⟩,
        ⟨1502, false, false, [220], [77221, 5, 15]⟩,
        ⟨917, true, false, [220, 199], [5, 15]⟩,
        ⟨606, true, false, [220, 199], [5, 15]⟩,
        ⟨1473, true, false, [220], [15, 5, 15]⟩,
        ⟨1504, false, false, [220, 77355], []⟩,
        ⟨1486, false, false, [220], []⟩,
        ⟨1488, false, false, [220], []⟩,
        ⟨1507, true, false, [], [77355]⟩,
        ⟨1507, true, false, [], [77355]⟩,
        ⟨1506, true, false, [], [77355]⟩,
        ⟨1551, false, false, [], []⟩,
        ⟨1551, false, false, [], []⟩
      ]⟩,
    ⟨[247], [223, 231], .source 188⟩,
    ⟨[247, 77349], [247, 77349], .contexts []⟩,
    ⟨[15, 3, 15, 3], [], .contexts [
        ⟨33, false, false, [], []⟩
      ]⟩,
    ⟨[77349, 3], [77349, 3], .contexts []⟩,
    ⟨[249], [246], .source 189⟩,
    ⟨[246], [246], .contexts []⟩,
    ⟨[77349, 3], [249, 77355], .contexts [
        ⟨1556, false, false, [], []⟩,
        ⟨1554, true, false, [246], [3]⟩,
        ⟨1350, true, false, [], [3]⟩,
        ⟨1553, false, false, [246], [77351, 15, 3]⟩,
        ⟨1522, true, false, [246, 223], [15, 3]⟩,
        ⟨1358, true, false, [246, 223], [15, 3]⟩,
        ⟨1552, true, false, [246], [3, 15, 3]⟩,
        ⟨1555, false, false, [246, 77355], []⟩,
        ⟨1486, false, false, [246], []⟩,
        ⟨1488, false, false, [246], []⟩,
        ⟨1558, true, false, [], [77355]⟩,
        ⟨1558, true, false, [], [77355]⟩,
        ⟨1557, true, false, [], [77355]⟩
      ]⟩,
    ⟨[251], [229, 247], .source 190⟩,
    ⟨[77351], [251, 77349], .contexts [
        ⟨1530, true, false, [230], []⟩,
        ⟨1559, true, false, [230, 248], [3]⟩,
        ⟨35, false, false, [230, 248, 77349], []⟩,
        ⟨1557, false, true, [230], [77349]⟩,
        ⟨1554, false, false, [230], []⟩,
        ⟨1519, false, true, [], [247, 77349]⟩,
        ⟨1560, true, false, [], [77349]⟩
      ]⟩,
    ⟨[253], [231, 251], .source 191⟩,
    ⟨[77353], [253, 77349], .contexts [
        ⟨1522, false, false, [], []⟩,
        ⟨1561, false, false, [231], []⟩,
        ⟨1562, true, false, [], [77349]⟩
      ]⟩,
    ⟨[255], [250], .source 192⟩,
    ⟨[257], [255, 253], .source 193⟩,
    ⟨[77349, 1], [257, 77349], .contexts [
        ⟨1561, true, false, [250], [1]⟩,
        ⟨1352, false, false, [250], []⟩,
        ⟨1563, false, false, [250], []⟩,
        ⟨1564, true, false, [], [253, 77349]⟩,
        ⟨1565, true, false, [], [77349]⟩
      ]⟩,
    ⟨[251, 77349], [251, 77349], .contexts []⟩,
    ⟨[77351], [251, 77349], .contexts [
        ⟨1561, false, false, [], []⟩,
        ⟨1567, false, false, [], []⟩
      ]⟩,
    ⟨[259], [255, 225], .source 194⟩,
    ⟨[261], [259, 251], .source 195⟩,
    ⟨[77349, 5], [261, 77349], .contexts [
        ⟨1561, true, false, [250], [5]⟩,
        ⟨1354, true, false, [250], [5]⟩,
        ⟨1477, true, false, [250, 204], [1, 5]⟩,
        ⟨1508, true, false, [250, 204], [1, 5]⟩,
        ⟨1509, false, false, [250, 204, 77353], []⟩,
        ⟨19, false, false, [250, 204, 77353], []⟩,
        ⟨1360, false, false, [250, 204], []⟩,
        ⟨1510, false, false, [250, 204], []⟩,
        ⟨1512, true, false, [250], [77351]⟩,
        ⟨1512, true, false, [250], [77351]⟩,
        ⟨1511, true, false, [250], [77351]⟩,
        ⟨1568, false, false, [250, 225], []⟩,
        ⟨1564, true, false, [], [225, 251, 77349]⟩,
        ⟨1569, true, false, [], [251, 77349]⟩,
        ⟨1570, true, false, [], [77349]⟩
      ]⟩,
    ⟨[263], [255, 237], .source 196⟩,
    ⟨[265], [263, 251], .source 197⟩,
    ⟨[77349, 9], [265, 77349], .contexts [
        ⟨1561, true, false, [250], [9]⟩,
        ⟨1529, false, false, [250, 232], [77351, 9]⟩,
        ⟨1522, true, false, [250, 232, 217], [9]⟩,
        ⟨1358, true, false, [250, 232, 217], [9]⟩,
        ⟨1528, true, false, [250, 232], [3, 9]⟩,
        ⟨841, false, false, [250, 232, 77355], []⟩,
        ⟨36, false, false, [250, 232, 77355], []⟩,
        ⟨1530, false, false, [250, 232], []⟩,
        ⟨1510, false, false, [250, 232, 231], []⟩,
        ⟨1531, true, false, [250], [231, 77351]⟩,
        ⟨1532, true, false, [250], [77351]⟩,
        ⟨1568, false, false, [250, 237], []⟩,
        ⟨1564, true, false, [], [237, 251, 77349]⟩,
        ⟨1572, true, false, [], [251, 77349]⟩,
        ⟨1573, true, false, [], [77349]⟩
      ]⟩,
    ⟨[261, 77349], [261, 77349], .contexts []⟩,
    ⟨[77349, 5], [261, 77349], .contexts [
        ⟨1571, false, false, [], []⟩,
        ⟨1575, false, false, [], []⟩,
        ⟨1575, false, false, [], []⟩
      ]⟩,
    ⟨[77349, 13], [77347], .contexts [
        ⟨1362, false, false, [], []⟩,
        ⟨1363, false, false, [], []⟩,
        ⟨1345, false, false, [], []⟩,
        ⟨1345, false, false, [], []⟩
      ]⟩,
    ⟨[5, 13, 5], [12], .contexts [
        ⟨282, false, false, [], [12]⟩
      ]⟩,
    ⟨[77349, 12], [77349, 13], .contexts [
        ⟨108, false, false, [77349], []⟩
      ]⟩,
    ⟨[77347, 5], [77347, 5], .contexts []⟩,
    ⟨[77347], [77347], .contexts []⟩,
    ⟨[267], [260], .source 198⟩,
    ⟨[260], [260], .contexts []⟩,
    ⟨[267], [260], .contexts [
        ⟨1582, false, false, [], []⟩,
        ⟨1583, false, false, [], []⟩,
        ⟨1583, false, false, [], []⟩
      ]⟩,
    ⟨[257, 77349], [257, 77349], .contexts []⟩,
    ⟨[77349, 1], [257, 77349], .contexts [
        ⟨1566, false, false, [], []⟩,
        ⟨1585, false, false, [], []⟩,
        ⟨1585, false, false, [], []⟩
      ]⟩,
    ⟨[1, 13, 1, 13], [12, 0], .contexts [
        ⟨188, false, false, [], [12, 0]⟩
      ]⟩,
    ⟨[77345, 13], [77345, 13], .contexts []⟩,
    ⟨[77345], [77345], .contexts []⟩,
    ⟨[269], [256], .source 199⟩,
    ⟨[256], [256], .contexts []⟩,
    ⟨[269], [256], .contexts [
        ⟨1590, false, false, [], []⟩,
        ⟨1591, false, false, [], []⟩,
        ⟨1591, false, false, [], []⟩
      ]⟩,
    ⟨[77345, 13], [269, 77345], .contexts [
        ⟨1588, false, false, [], []⟩,
        ⟨1342, true, false, [], [13]⟩,
        ⟨1346, true, false, [], [1, 13]⟩,
        ⟨1586, true, false, [256], [13, 1, 13]⟩,
        ⟨1587, false, false, [256, 77349], []⟩,
        ⟨190, false, false, [256, 77349], []⟩,
        ⟨1577, false, false, [256], [1]⟩,
        ⟨1364, false, false, [256], []⟩,
        ⟨1365, false, false, [256], []⟩,
        ⟨1341, false, false, [256], []⟩,
        ⟨1341, false, false, [256], []⟩,
        ⟨1589, false, false, [256], []⟩,
        ⟨1592, true, false, [], [77345]⟩
      ]⟩,
    ⟨[265, 77349], [265, 77349], .contexts []⟩,
    ⟨[77347, 9], [77347, 9], .contexts []⟩,
    ⟨[271], [264], .source 200⟩,
    ⟨[264], [264], .contexts []⟩,
    ⟨[77347, 9], [271, 77347], .contexts [
        ⟨1595, false, false, [], []⟩,
        ⟨1346, true, false, [], [9]⟩,
        ⟨1594, true, false, [264], [13, 9]⟩,
        ⟨1594, true, false, [264], [13, 9]⟩,
        ⟨1574, true, false, [264], [13, 9]⟩,
        ⟨926, false, false, [264, 77349], []⟩,
        ⟨1579, false, false, [264], []⟩,
        ⟨1577, false, false, [264], []⟩,
        ⟨1581, false, false, [264], []⟩,
        ⟨1597, true, false, [], [77347]⟩,
        ⟨1597, true, false, [], [77347]⟩,
        ⟨1596, true, false, [], [77347]⟩
      ]⟩,
    ⟨[245, 77241], [245, 77241], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 025. -/
def y322TCContextRaw025 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[245, 77241], [245, 77241], .contexts []⟩,
    ⟨[77237, 13], [245, 77241], .contexts [
        ⟨1550, false, false, [], []⟩,
        ⟨1599, false, false, [], []⟩,
        ⟨1600, false, false, [], []⟩,
        ⟨1600, false, false, [], []⟩
      ]⟩,
    ⟨[77237, 12], [77237, 13], .contexts [
        ⟨108, false, false, [77237], []⟩
      ]⟩,
    ⟨[77115, 9], [77115, 9], .contexts []⟩,
    ⟨[77241], [77241], .contexts []⟩,
    ⟨[245, 77241], [245, 77241], .contexts [
        ⟨1604, false, false, [245], []⟩
      ]⟩,
    ⟨[245], [245], .contexts [
        ⟨24, false, false, [], [245]⟩,
        ⟨1542, false, false, [], []⟩,
        ⟨1543, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77241], [245, 77241], .contexts [
        ⟨1606, true, false, [], [77241]⟩
      ]⟩,
    ⟨[77115, 9], [245, 77241], .contexts [
        ⟨1603, false, false, [], []⟩,
        ⟨378, true, false, [], [9]⟩,
        ⟨378, true, false, [], [9]⟩,
        ⟨377, true, false, [], [9]⟩,
        ⟨376, true, false, [], [9]⟩,
        ⟨367, true, false, [], [13, 9]⟩,
        ⟨367, true, false, [], [13, 9]⟩,
        ⟨366, true, false, [], [13, 9]⟩,
        ⟨1132, true, false, [], [13, 9]⟩,
        ⟨926, false, false, [77237], []⟩,
        ⟨1602, false, false, [], []⟩,
        ⟨1601, false, false, [], []⟩,
        ⟨1605, false, false, [], []⟩,
        ⟨1607, false, false, [], []⟩
      ]⟩,
    ⟨[77239], [243, 77237], .contexts [
        ⟨1547, false, false, [], []⟩
      ]⟩,
    ⟨[77237, 11], [243, 77237], .contexts [
        ⟨1156, false, false, [], []⟩,
        ⟨1609, false, false, [], []⟩,
        ⟨1546, false, false, [], []⟩,
        ⟨1546, false, false, [], []⟩
      ]⟩,
    ⟨[77241, 11], [77241, 11], .contexts []⟩,
    ⟨[77241, 11], [245, 77241], .contexts [
        ⟨1611, false, false, [], []⟩,
        ⟨1540, true, false, [243], [77241, 11]⟩,
        ⟨1550, true, false, [243], [11]⟩,
        ⟨1610, true, false, [], [13, 11]⟩,
        ⟨1060, false, false, [77237], []⟩,
        ⟨1602, false, false, [], []⟩,
        ⟨1601, false, false, [], []⟩,
        ⟨1605, false, false, [], []⟩,
        ⟨1607, false, false, [], []⟩
      ]⟩,
    ⟨[267, 77347], [267, 77347], .contexts []⟩,
    ⟨[77347, 5, 1], [267, 77345], .contexts [
        ⟨1580, false, false, [], [1]⟩,
        ⟨1580, false, false, [], [1]⟩,
        ⟨1346, true, false, [], [5, 1]⟩,
        ⟨1576, true, false, [260], [13, 5, 1]⟩,
        ⟨1578, false, false, [260, 77349], [1]⟩,
        ⟨1579, false, false, [260], [1]⟩,
        ⟨1577, false, false, [260], [1]⟩,
        ⟨1581, false, false, [260], [1]⟩,
        ⟨1584, true, false, [], [77347, 1]⟩,
        ⟨1613, false, false, [], [1]⟩,
        ⟨1613, false, false, [], [1]⟩,
        ⟨1342, false, false, [267], []⟩
      ]⟩,
    ⟨[77347, 1], [77345], .contexts [
        ⟨1364, false, false, [], []⟩,
        ⟨1365, false, false, [], []⟩,
        ⟨1341, false, false, [], []⟩,
        ⟨1341, false, false, [], []⟩
      ]⟩,
    ⟨[77345, 5], [77345, 5], .contexts []⟩,
    ⟨[261], [266], .contexts [
        ⟨1582, true, true, [], []⟩
      ]⟩,
    ⟨[261], [261], .contexts []⟩,
    ⟨[266], [266], .contexts []⟩,
    ⟨[261], [266], .contexts [
        ⟨1618, false, false, [], []⟩,
        ⟨1617, false, false, [], []⟩,
        ⟨1619, false, false, [], []⟩,
        ⟨1619, false, false, [], []⟩
      ]⟩,
    ⟨[77345, 5], [261, 77345], .contexts [
        ⟨1616, false, false, [], []⟩,
        ⟨1614, true, false, [266], [5]⟩,
        ⟨1509, false, false, [266, 77347], []⟩,
        ⟨19, false, false, [266, 77347], []⟩,
        ⟨1615, false, false, [266], []⟩,
        ⟨1589, false, false, [266], []⟩,
        ⟨1620, true, false, [], [77345]⟩
      ]⟩,
    ⟨[269, 77345], [269, 77345], .contexts []⟩,
    ⟨[77345, 11], [77343], .contexts [
        ⟨1366, false, false, [], []⟩,
        ⟨1367, false, false, [], []⟩,
        ⟨1337, false, false, [], []⟩,
        ⟨1337, false, false, [], []⟩
      ]⟩,
    ⟨[13, 11, 13], [10], .contexts [
        ⟨136, false, false, [], [10]⟩
      ]⟩,
    ⟨[77345, 10], [77345, 11], .contexts [
        ⟨91, false, false, [77345], []⟩
      ]⟩,
    ⟨[77343, 13], [77343, 13], .contexts []⟩,
    ⟨[77343], [77343], .contexts []⟩,
    ⟨[268], [268], .contexts []⟩,
    ⟨[77343, 13], [257, 77343], .contexts [
        ⟨1626, false, false, [], []⟩,
        ⟨1338, true, false, [], [13]⟩,
        ⟨1622, true, false, [268], [11, 13]⟩,
        ⟨1622, true, false, [268], [11, 13]⟩,
        ⟨1593, true, false, [268], [11, 13]⟩,
        ⟨1588, true, false, [268], [11, 13]⟩,
        ⟨1624, false, false, [268, 77345], []⟩,
        ⟨1625, false, false, [268], []⟩,
        ⟨1623, false, false, [268], []⟩,
        ⟨1627, false, false, [268], []⟩,
        ⟨1628, true, false, [], [77343]⟩,
        ⟨1628, true, false, [], [77343]⟩,
        ⟨1590, false, true, [], [77343]⟩
      ]⟩,
    ⟨[77115, 9], [245, 77241], .contexts [
        ⟨1608, false, false, [], []⟩
      ]⟩,
    ⟨[77115, 9], [245, 77241], .contexts [
        ⟨1603, false, false, [], []⟩,
        ⟨1630, false, false, [], []⟩,
        ⟨1599, false, false, [], []⟩,
        ⟨1600, false, false, [], []⟩,
        ⟨1600, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77241, 15], [245, 77243], .contexts [
        ⟨1171, false, false, [245], []⟩
      ]⟩,
    ⟨[245, 77243], [245, 77243], .contexts []⟩,
    ⟨[245, 77243], [245, 77243], .contexts []⟩,
    ⟨[245, 77243], [245, 77243], .contexts []⟩,
    ⟨[9, 15, 9], [14], .contexts [
        ⟨322, false, false, [], [14]⟩
      ]⟩,
    ⟨[77243, 9], [77243, 9], .contexts []⟩,
    ⟨[244], [244], .contexts []⟩,
    ⟨[243], [244], .contexts [
        ⟨1544, false, false, [], []⟩,
        ⟨1638, false, false, [], []⟩,
        ⟨1638, false, false, [], []⟩
      ]⟩,
    ⟨[77243, 9], [243, 77117], .contexts [
        ⟨1637, false, false, [], []⟩,
        ⟨1635, true, false, [244], [9]⟩,
        ⟨1634, true, false, [244], [9]⟩,
        ⟨1633, true, false, [244], [9]⟩,
        ⟨1632, true, false, [244], [9]⟩,
        ⟨1631, true, false, [244], [15, 9]⟩,
        ⟨1636, false, false, [244, 77115], []⟩,
        ⟨20, false, false, [244, 77115], []⟩,
        ⟨399, false, false, [244], []⟩,
        ⟨402, false, false, [244], []⟩,
        ⟨1639, true, false, [], [77117]⟩
      ]⟩,
    ⟨[77117, 9], [245, 77243], .contexts [
        ⟨1640, true, false, [242], [9]⟩,
        ⟨76, false, false, [242, 77243], []⟩,
        ⟨1540, true, false, [], [77243]⟩
      ]⟩,
    ⟨[77243, 11], [77243, 11], .contexts []⟩,
    ⟨[77243, 11], [243, 77243], .contexts [
        ⟨1642, false, false, [], []⟩,
        ⟨1635, true, false, [244], [11]⟩,
        ⟨1634, true, false, [244], [11]⟩,
        ⟨1633, true, false, [244], [11]⟩,
        ⟨1632, true, false, [244], [11]⟩,
        ⟨1600, true, false, [244], [15, 11]⟩,
        ⟨1600, true, false, [244], [15, 11]⟩,
        ⟨1599, true, false, [244], [15, 11]⟩,
        ⟨1612, true, false, [244], [15, 11]⟩,
        ⟨1611, true, false, [244], [15, 11]⟩,
        ⟨1054, false, false, [244, 77241], []⟩,
        ⟨20, false, false, [244, 77241], []⟩,
        ⟨1175, false, false, [244], []⟩,
        ⟨1181, false, false, [244], []⟩,
        ⟨1639, true, false, [], [77243]⟩
      ]⟩,
    ⟨[261, 77345], [261, 77345], .contexts []⟩,
    ⟨[5, 11, 5], [10], .contexts [
        ⟨274, false, false, [], [10]⟩
      ]⟩,
    ⟨[77343, 5], [77343, 5], .contexts []⟩,
    ⟨[77343, 5], [267, 77343], .contexts [
        ⟨1646, false, false, [], []⟩,
        ⟨1338, true, false, [], [5]⟩,
        ⟨1644, true, false, [260], [11, 5]⟩,
        ⟨1644, true, false, [260], [11, 5]⟩,
        ⟨1621, true, false, [260], [11, 5]⟩,
        ⟨1616, true, false, [260], [11, 5]⟩,
        ⟨1645, false, false, [260, 77345], []⟩,
        ⟨1625, false, false, [260], []⟩,
        ⟨1623, false, false, [260], []⟩,
        ⟨1627, false, false, [260], []⟩,
        ⟨1584, true, false, [], [77343]⟩
      ]⟩,
    ⟨[257, 77343], [257, 77343], .contexts []⟩,
    ⟨[77343, 9], [77341], .contexts [
        ⟨1368, false, false, [], []⟩,
        ⟨1369, false, false, [], []⟩,
        ⟨1333, false, false, [], []⟩,
        ⟨1333, false, false, [], []⟩
      ]⟩,
    ⟨[13, 9, 13], [8], .contexts [
        ⟨129, false, false, [], [8]⟩
      ]⟩,
    ⟨[77343, 8], [77343, 9], .contexts [
        ⟨77, false, false, [77343], []⟩
      ]⟩,
    ⟨[77341, 13], [77341, 13], .contexts []⟩,
    ⟨[77341], [77341], .contexts []⟩,
    ⟨[77341, 13], [269, 77341], .contexts [
        ⟨1652, false, false, [], []⟩,
        ⟨1334, true, false, [], [13]⟩,
        ⟨1648, true, false, [256], [9, 13]⟩,
        ⟨1648, true, false, [256], [9, 13]⟩,
        ⟨1629, true, false, [256], [9, 13]⟩,
        ⟨1626, true, false, [256], [9, 13]⟩,
        ⟨1650, false, false, [256, 77343], []⟩,
        ⟨1651, false, false, [256], []⟩,
        ⟨1649, false, false, [256], []⟩,
        ⟨1653, false, false, [256], []⟩,
        ⟨1592, true, false, [], [77341]⟩
      ]⟩,
    ⟨[243, 77117], [243, 77117], .contexts []⟩,
    ⟨[273], [243, 19], .source 201⟩,
    ⟨[275], [273, 245], .source 202⟩,
    ⟨[77243, 1], [77245], .contexts [
        ⟨1183, false, false, [], []⟩
      ]⟩,
    ⟨[77243, 1], [77245], .contexts [
        ⟨1658, false, false, [], []⟩,
        ⟨1426, false, false, [], []⟩,
        ⟨1187, false, false, [], []⟩,
        ⟨1187, false, false, [], []⟩
      ]⟩,
    ⟨[77243, 0], [77243, 1], .contexts [
        ⟨19, false, false, [77243], []⟩
      ]⟩,
    ⟨[275, 77245, 9], [77245], .contexts [
        ⟨1183, true, false, [275], [9]⟩,
        ⟨1657, false, false, [], [77243, 1, 9]⟩,
        ⟨1641, true, false, [273], [1, 9]⟩,
        ⟨1656, false, false, [], [77117, 9, 1, 9]⟩,
        ⟨735, false, false, [243], [77117, 9, 1, 9]⟩,
        ⟨403, true, false, [243], [9, 1, 9]⟩,
        ⟨1655, true, false, [], [1, 9, 1, 9]⟩,
        ⟨1655, true, false, [], [1, 9, 1, 9]⟩,
        ⟨1640, true, false, [], [1, 9, 1, 9]⟩,
        ⟨1637, true, false, [], [1, 9, 1, 9]⟩,
        ⟨885, false, false, [77243], []⟩,
        ⟨1660, false, false, [], []⟩,
        ⟨1659, false, false, [], []⟩
      ]⟩,
    ⟨[77245, 9], [77245, 9], .contexts []⟩,
    ⟨[77245], [77245], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 026. -/
def y322TCContextRaw026 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[277], [274], .source 203⟩,
    ⟨[277], [274], .contexts [
        ⟨1664, false, false, [], []⟩
      ]⟩,
    ⟨[274], [274], .contexts []⟩,
    ⟨[277], [274], .contexts [
        ⟨1665, false, false, [], []⟩,
        ⟨1666, false, false, [], []⟩,
        ⟨1666, false, false, [], []⟩
      ]⟩,
    ⟨[243, 77243], [243, 77243], .contexts []⟩,
    ⟨[77245, 11], [77245, 11], .contexts []⟩,
    ⟨[245], [242], .contexts [
        ⟨1541, false, false, [], []⟩,
        ⟨1548, false, false, [], []⟩,
        ⟨1549, false, false, [], []⟩,
        ⟨1549, false, false, [], []⟩
      ]⟩,
    ⟨[267, 77343], [267, 77343], .contexts []⟩,
    ⟨[5, 9, 5], [8], .contexts [
        ⟨1496, false, false, [], [8]⟩
      ]⟩,
    ⟨[77341, 5], [77341, 5], .contexts []⟩,
    ⟨[77341, 5], [261, 77341], .contexts [
        ⟨1673, false, false, [], []⟩,
        ⟨1334, true, false, [], [5]⟩,
        ⟨1671, true, false, [266], [9, 5]⟩,
        ⟨1671, true, false, [266], [9, 5]⟩,
        ⟨1647, true, false, [266], [9, 5]⟩,
        ⟨1646, true, false, [266], [9, 5]⟩,
        ⟨1672, false, false, [266, 77343], []⟩,
        ⟨1651, false, false, [266], []⟩,
        ⟨1649, false, false, [266], []⟩,
        ⟨1653, false, false, [266], []⟩,
        ⟨1620, true, false, [], [77341]⟩
      ]⟩,
    ⟨[277, 77245], [277, 77245], .contexts []⟩,
    ⟨[77245, 9], [277, 77245], .contexts [
        ⟨1662, false, false, [], []⟩,
        ⟨1662, false, false, [], []⟩,
        ⟨1661, false, false, [274], []⟩,
        ⟨1663, false, false, [274], []⟩,
        ⟨1667, true, false, [], [77245]⟩,
        ⟨1675, false, false, [], []⟩,
        ⟨1675, false, false, [], []⟩
      ]⟩,
    ⟨[77245, 3], [77247], .contexts [
        ⟨1186, false, false, [], []⟩
      ]⟩,
    ⟨[77245, 3], [77247], .contexts [
        ⟨1677, false, false, [], []⟩,
        ⟨1425, false, false, [], []⟩,
        ⟨1190, false, false, [], []⟩,
        ⟨1190, false, false, [], []⟩
      ]⟩,
    ⟨[77245, 2], [77245, 3], .contexts [
        ⟨36, false, false, [77245], []⟩
      ]⟩,
    ⟨[77247, 9], [77247, 9], .contexts []⟩,
    ⟨[77247], [77247], .contexts []⟩,
    ⟨[275], [276], .contexts [
        ⟨1664, true, true, [], []⟩
      ]⟩,
    ⟨[275], [275], .contexts []⟩,
    ⟨[275], [276], .contexts [
        ⟨1682, false, false, [], []⟩
      ]⟩,
    ⟨[276], [276], .contexts []⟩,
    ⟨[275], [276], .contexts [
        ⟨1683, false, false, [], []⟩,
        ⟨1684, false, false, [], []⟩,
        ⟨1685, false, false, [], []⟩,
        ⟨1685, false, false, [], []⟩
      ]⟩,
    ⟨[77247, 9], [275, 77247], .contexts [
        ⟨1680, false, false, [], []⟩,
        ⟨1186, true, false, [], [9]⟩,
        ⟨1676, true, false, [276], [3, 9]⟩,
        ⟨841, false, false, [276, 77245], []⟩,
        ⟨1679, false, false, [276], []⟩,
        ⟨1678, false, false, [276], []⟩,
        ⟨1681, false, false, [276], []⟩,
        ⟨1686, true, false, [], [77247]⟩
      ]⟩,
    ⟨[245, 77245], [245, 77245], .contexts []⟩,
    ⟨[245, 77245], [245, 77245], .contexts []⟩,
    ⟨[77245, 11], [245, 77245], .contexts [
        ⟨1669, false, false, [], []⟩,
        ⟨1669, false, false, [], []⟩,
        ⟨1183, true, false, [], [11]⟩,
        ⟨1668, true, false, [242], [1, 11]⟩,
        ⟨1668, true, false, [242], [1, 11]⟩,
        ⟨1643, true, false, [242], [1, 11]⟩,
        ⟨1642, true, false, [242], [1, 11]⟩,
        ⟨1000, false, false, [242, 77243], []⟩,
        ⟨1660, false, false, [242], []⟩,
        ⟨1659, false, false, [242], []⟩,
        ⟨1663, false, false, [242], []⟩,
        ⟨1670, true, false, [], [77245]⟩,
        ⟨1688, false, false, [], []⟩,
        ⟨1689, false, false, [], []⟩,
        ⟨1689, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77245, 3], [245, 77247], .contexts [
        ⟨1186, false, false, [245], []⟩
      ]⟩,
    ⟨[245, 77247], [245, 77247], .contexts []⟩,
    ⟨[245, 77247], [245, 77247], .contexts []⟩,
    ⟨[245, 77247], [245, 77247], .contexts []⟩,
    ⟨[77247, 11], [77247, 11], .contexts []⟩,
    ⟨[77247, 11], [243, 77247], .contexts [
        ⟨1695, false, false, [], []⟩,
        ⟨1694, true, false, [244], [11]⟩,
        ⟨1693, true, false, [244], [11]⟩,
        ⟨1692, true, false, [244], [11]⟩,
        ⟨1691, true, false, [244], [11]⟩,
        ⟨1690, true, false, [244], [3, 11]⟩,
        ⟨1040, false, false, [244, 77245], []⟩,
        ⟨1679, false, false, [244], []⟩,
        ⟨1678, false, false, [244], []⟩,
        ⟨1681, false, false, [244], []⟩,
        ⟨1639, true, false, [], [77247]⟩
      ]⟩,
    ⟨[261, 77341], [261, 77341], .contexts []⟩,
    ⟨[77341, 5], [261, 77341], .contexts [
        ⟨1673, false, false, [], []⟩,
        ⟨1674, false, false, [], []⟩,
        ⟨1697, false, false, [], []⟩,
        ⟨1697, false, false, [], []⟩
      ]⟩,
    ⟨[261, 77337], [261, 77337], .contexts []⟩,
    ⟨[261, 77337], [261, 77337], .contexts []⟩,
    ⟨[77337, 1], [267, 77341], .contexts [
        ⟨1700, true, false, [260], [1]⟩,
        ⟨1699, true, false, [260], [1]⟩,
        ⟨1327, true, false, [], [1]⟩,
        ⟨1330, true, false, [], [5, 1]⟩,
        ⟨1698, true, false, [260], [1, 5, 1]⟩,
        ⟨1485, false, false, [260, 77341], []⟩,
        ⟨1653, false, false, [260], []⟩,
        ⟨1584, true, false, [], [77341]⟩
      ]⟩,
    ⟨[77341, 1], [77339], .contexts [
        ⟨1371, false, false, [], []⟩
      ]⟩,
    ⟨[261], [261], .contexts []⟩,
    ⟨[261], [261], .contexts []⟩,
    ⟨[275, 77247], [275, 77247], .contexts []⟩,
    ⟨[77247, 5], [77249], .contexts [
        ⟨1189, false, false, [], []⟩
      ]⟩,
    ⟨[77247, 5], [77249], .contexts [
        ⟨1706, false, false, [], []⟩,
        ⟨1423, false, false, [], []⟩,
        ⟨1193, false, false, [], []⟩,
        ⟨1193, false, false, [], []⟩
      ]⟩,
    ⟨[77247, 4], [77247, 5], .contexts [
        ⟨50, false, false, [77247], []⟩
      ]⟩,
    ⟨[77249, 9], [77249, 9], .contexts []⟩,
    ⟨[77249], [77249], .contexts []⟩,
    ⟨[243, 77247], [243, 77247], .contexts []⟩,
    ⟨[77249, 11], [77249, 11], .contexts []⟩,
    ⟨[277, 77249], [277, 77249], .contexts []⟩,
    ⟨[77249, 9], [277, 77249], .contexts [
        ⟨1709, false, false, [], []⟩,
        ⟨1709, false, false, [], []⟩,
        ⟨1189, true, false, [], [9]⟩,
        ⟨1705, true, false, [274], [5, 9]⟩,
        ⟨1705, true, false, [274], [5, 9]⟩,
        ⟨1687, true, false, [274], [5, 9]⟩,
        ⟨1680, true, false, [274], [5, 9]⟩,
        ⟨1034, false, false, [274, 77247], []⟩,
        ⟨1708, false, false, [274], []⟩,
        ⟨1707, false, false, [274], []⟩,
        ⟨1710, false, false, [274], []⟩,
        ⟨1667, true, false, [], [77249]⟩,
        ⟨1713, false, false, [], []⟩,
        ⟨1713, false, false, [], []⟩
      ]⟩,
    ⟨[77249, 1], [77251], .contexts [
        ⟨1192, false, false, [], []⟩,
        ⟨1421, false, false, [], []⟩,
        ⟨1196, false, false, [], []⟩,
        ⟨1196, false, false, [], []⟩
      ]⟩,
    ⟨[77251, 9], [77253], .contexts [
        ⟨1195, false, false, [], []⟩
      ]⟩,
    ⟨[9, 1, 9, 1], [0, 8], .contexts [
        ⟨884, false, false, [], [0, 8]⟩
      ]⟩,
    ⟨[77253, 1], [77253, 1], .contexts []⟩,
    ⟨[77253], [77253], .contexts []⟩,
    ⟨[77253, 1], [275, 77253], .contexts [
        ⟨1718, false, false, [], []⟩,
        ⟨1195, true, false, [], [1]⟩,
        ⟨1192, true, false, [], [9, 1]⟩,
        ⟨1714, true, false, [276], [1, 9, 1]⟩,
        ⟨1717, false, false, [276, 77249], []⟩,
        ⟨1144, false, false, [276, 77249], []⟩,
        ⟨1715, false, false, [276], [9]⟩,
        ⟨1716, false, false, [276], []⟩,
        ⟨1420, false, false, [276], []⟩,
        ⟨1199, false, false, [276], []⟩,
        ⟨1199, false, false, [276], []⟩,
        ⟨1719, false, false, [276], []⟩,
        ⟨1686, true, false, [], [77253]⟩
      ]⟩,
    ⟨[245, 77249], [245, 77249], .contexts []⟩,
    ⟨[77249, 11], [245, 77249], .contexts [
        ⟨1712, false, false, [], []⟩,
        ⟨1712, false, false, [], []⟩,
        ⟨1189, true, false, [], [11]⟩,
        ⟨1711, true, false, [242], [5, 11]⟩,
        ⟨1711, true, false, [242], [5, 11]⟩,
        ⟨1696, true, false, [242], [5, 11]⟩,
        ⟨1695, true, false, [242], [5, 11]⟩,
        ⟨1028, false, false, [242, 77247], []⟩,
        ⟨1708, false, false, [242], []⟩,
        ⟨1707, false, false, [242], []⟩,
        ⟨1710, false, false, [242], []⟩,
        ⟨1670, true, false, [], [77249]⟩,
        ⟨1721, false, false, [], []⟩,
        ⟨1721, false, false, [], []⟩
      ]⟩,
    ⟨[77251, 11], [77251, 11], .contexts []⟩,
    ⟨[77251], [77251], .contexts []⟩,
    ⟨[77251, 11], [243, 77251], .contexts [
        ⟨1723, false, false, [], []⟩,
        ⟨1192, true, false, [], [11]⟩,
        ⟨1722, true, false, [244], [1, 11]⟩,
        ⟨1000, false, false, [244, 77249], []⟩,
        ⟨19, false, false, [244, 77249], []⟩,
        ⟨1715, false, false, [244], []⟩,
        ⟨1724, false, false, [244], []⟩,
        ⟨1639, true, false, [], [77251]⟩
      ]⟩,
    ⟨[275, 77253], [275, 77253], .contexts []⟩,
    ⟨[275, 77257], [275, 77257], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 027. -/
def y322TCContextRaw027 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1, 11, 1, 11], [], .contexts [
        ⟨180, false, false, [], []⟩
      ]⟩,
    ⟨[77257, 11], [277, 77253], .contexts [
        ⟨1727, true, false, [274], [11]⟩,
        ⟨1201, true, false, [], [11]⟩,
        ⟨1198, true, false, [], [1, 11]⟩,
        ⟨1726, true, false, [274], [11, 1, 11]⟩,
        ⟨1726, true, false, [274], [11, 1, 11]⟩,
        ⟨1720, true, false, [274], [11, 1, 11]⟩,
        ⟨1718, true, false, [274], [11, 1, 11]⟩,
        ⟨1728, false, false, [274, 77253], []⟩,
        ⟨1719, false, false, [274], []⟩,
        ⟨1667, true, false, [], [77253]⟩
      ]⟩,
    ⟨[77253, 11], [77255], .contexts [
        ⟨1198, false, false, [], []⟩
      ]⟩,
    ⟨[77253, 11], [77255], .contexts [
        ⟨1730, false, false, [], []⟩,
        ⟨1419, false, false, [], []⟩,
        ⟨1202, false, false, [], []⟩,
        ⟨1202, false, false, [], []⟩
      ]⟩,
    ⟨[275], [275], .contexts []⟩,
    ⟨[275], [275], .contexts []⟩,
    ⟨[77257], [277, 77255], .contexts [
        ⟨1683, false, false, [274], [77257]⟩,
        ⟨1732, false, false, [274], [77257]⟩,
        ⟨1733, false, false, [274], [77257]⟩,
        ⟨1727, true, false, [274], []⟩,
        ⟨1682, false, false, [274], [77257]⟩,
        ⟨90, true, false, [274, 276, 77257], []⟩,
        ⟨1729, false, false, [274, 276], [11]⟩,
        ⟨1731, false, false, [274], []⟩,
        ⟨1664, true, false, [], [77255]⟩
      ]⟩,
    ⟨[77255, 13], [275, 77259], .contexts [
        ⟨1734, true, false, [276], [13]⟩,
        ⟨1204, false, false, [276], []⟩,
        ⟨1418, false, false, [276], []⟩,
        ⟨1685, true, false, [], [77259]⟩,
        ⟨1685, true, false, [], [77259]⟩,
        ⟨1684, true, false, [], [77259]⟩
      ]⟩,
    ⟨[243, 77251], [243, 77251], .contexts []⟩,
    ⟨[77251, 9], [77253], .contexts [
        ⟨1716, false, false, [], []⟩,
        ⟨1420, false, false, [], []⟩,
        ⟨1199, false, false, [], []⟩,
        ⟨1199, false, false, [], []⟩
      ]⟩,
    ⟨[11, 9, 11, 9], [8, 10], .contexts [
        ⟨343, false, false, [], [8, 10]⟩
      ]⟩,
    ⟨[77255, 9], [77255, 9], .contexts []⟩,
    ⟨[77255], [77255], .contexts []⟩,
    ⟨[77255, 9], [245, 77255], .contexts [
        ⟨1739, false, false, [], []⟩,
        ⟨1198, true, false, [], [9]⟩,
        ⟨1195, true, false, [], [11, 9]⟩,
        ⟨1736, true, false, [242], [9, 11, 9]⟩,
        ⟨1736, true, false, [242], [9, 11, 9]⟩,
        ⟨1725, true, false, [242], [9, 11, 9]⟩,
        ⟨1723, true, false, [242], [9, 11, 9]⟩,
        ⟨1738, false, false, [242, 77251], []⟩,
        ⟨345, false, false, [242, 77251], []⟩,
        ⟨1737, false, false, [242], [11]⟩,
        ⟨1730, false, false, [242], []⟩,
        ⟨1419, false, false, [242], []⟩,
        ⟨1202, false, false, [242], []⟩,
        ⟨1202, false, false, [242], []⟩,
        ⟨1740, false, false, [242], []⟩,
        ⟨1670, true, false, [], [77255]⟩
      ]⟩,
    ⟨[77255, 13], [275, 77259], .contexts [
        ⟨1735, false, false, [], []⟩
      ]⟩,
    ⟨[275, 77259], [275, 77259], .contexts []⟩,
    ⟨[275, 77259], [275, 77259], .contexts []⟩,
    ⟨[77255, 13], [275, 77259], .contexts [
        ⟨1742, false, false, [], []⟩,
        ⟨1743, false, false, [], []⟩,
        ⟨1744, false, false, [], []⟩,
        ⟨1744, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77255], [245, 77255], .contexts []⟩,
    ⟨[279], [245, 275], .source 204⟩,
    ⟨[77259, 9], [77259, 9], .contexts []⟩,
    ⟨[77259], [77259], .contexts []⟩,
    ⟨[281], [277, 279], .source 205⟩,
    ⟨[281, 77259], [281, 77259], .contexts []⟩,
    ⟨[77259, 9, 15], [281, 77261], .contexts [
        ⟨1748, false, false, [], [15]⟩,
        ⟨1748, false, false, [], [15]⟩,
        ⟨1745, true, false, [274], [9, 15]⟩,
        ⟨130, false, false, [274, 77255], [15]⟩,
        ⟨131, false, false, [274, 77255], [15]⟩,
        ⟨1739, false, false, [274], [13, 15]⟩,
        ⟨1741, false, false, [274], [13, 15]⟩,
        ⟨1746, false, false, [274], [13, 15]⟩,
        ⟨1746, false, false, [274], [13, 15]⟩,
        ⟨1735, false, false, [274, 245], [15]⟩,
        ⟨1747, true, false, [274], [77259, 15]⟩,
        ⟨1749, false, false, [274, 279], [15]⟩,
        ⟨1665, true, false, [], [279, 77259, 15]⟩,
        ⟨1750, true, false, [], [77259, 15]⟩,
        ⟨1751, false, false, [], [15]⟩,
        ⟨1751, false, false, [], [15]⟩,
        ⟨1207, false, false, [281], []⟩
      ]⟩,
    ⟨[77259, 15], [77261], .contexts [
        ⟨1207, false, false, [], []⟩,
        ⟨1416, false, false, [], []⟩,
        ⟨1212, false, false, [], []⟩,
        ⟨1212, false, false, [], []⟩
      ]⟩,
    ⟨[77259, 14], [77259, 15], .contexts [
        ⟨20, false, false, [77259], []⟩
      ]⟩,
    ⟨[77261], [77261], .contexts []⟩,
    ⟨[283], [280], .source 206⟩,
    ⟨[280], [280], .contexts []⟩,
    ⟨[77261, 9], [283, 77261], .contexts [
        ⟨1752, true, false, [280], [9]⟩,
        ⟨1636, false, false, [280, 77259], []⟩,
        ⟨1754, false, false, [280], []⟩,
        ⟨1753, false, false, [280], []⟩,
        ⟨1755, false, false, [280], []⟩,
        ⟨1757, true, false, [], [77261]⟩,
        ⟨1757, true, false, [], [77261]⟩,
        ⟨1756, true, false, [], [77261]⟩
      ]⟩,
    ⟨[77357], [77107, 7], .source 38743⟩,
    ⟨[77107, 7], [77357], .contexts [
        ⟨1759, true, false, [], []⟩
      ]⟩,
    ⟨[77357], [77357], .contexts []⟩,
    ⟨[77357], [77357], .contexts []⟩,
    ⟨[77107, 7], [77357], .contexts [
        ⟨1760, false, false, [], []⟩,
        ⟨1761, false, false, [], []⟩,
        ⟨1762, false, false, [], []⟩,
        ⟨1762, false, false, [], []⟩
      ]⟩,
    ⟨[7, 1], [0, 6], .contexts [
        ⟨905, false, false, [], [0, 6]⟩
      ]⟩,
    ⟨[0, 6], [1, 7], .contexts [
        ⟨19, false, false, [], [6]⟩,
        ⟨63, false, false, [1], []⟩
      ]⟩,
    ⟨[77357], [77357], .contexts []⟩,
    ⟨[5, 77357], [5, 77357], .contexts []⟩,
    ⟨[5, 77357], [5, 77357], .contexts []⟩,
    ⟨[7, 3], [2, 6], .contexts [
        ⟨223, false, false, [2], [6]⟩
      ]⟩,
    ⟨[2, 6], [3, 7], .contexts [
        ⟨36, false, false, [], [6]⟩,
        ⟨63, false, false, [3], []⟩
      ]⟩,
    ⟨[77357, 3], [77357, 3], .contexts []⟩,
    ⟨[77107, 5, 7, 5], [7, 77107], .contexts [
        ⟨251, false, false, [], [7, 5]⟩,
        ⟨206, false, false, [], [7, 5]⟩,
        ⟨207, false, false, [], [7, 5]⟩,
        ⟨207, false, false, [], [7, 5]⟩,
        ⟨208, true, false, [], [7, 5]⟩,
        ⟨225, false, false, [77103], [5]⟩,
        ⟨226, false, false, [77103], [5]⟩,
        ⟨175, false, false, [], [3, 5]⟩,
        ⟨176, false, false, [], [3, 5]⟩,
        ⟨169, false, false, [], [3, 5]⟩,
        ⟨170, false, false, [], [3, 5]⟩,
        ⟨170, false, false, [], [3, 5]⟩,
        ⟨204, false, false, [7], [5]⟩,
        ⟨221, false, false, [], [5]⟩,
        ⟨222, false, false, [], [5]⟩,
        ⟨218, false, false, [7], [5]⟩,
        ⟨66, true, false, [], [77105, 5]⟩,
        ⟨221, false, false, [], [5]⟩,
        ⟨222, false, false, [], [5]⟩,
        ⟨222, false, false, [], [5]⟩,
        ⟨250, false, false, [7], []⟩
      ]⟩,
    ⟨[7, 77357], [7, 77357], .contexts []⟩,
    ⟨[7, 77357], [7, 77357], .contexts []⟩,
    ⟨[5, 7, 5, 7, 5, 7], [], .source 27⟩,
    ⟨[7, 5], [4, 6, 4, 6], .contexts [
        ⟨1775, false, false, [4], [6, 4, 6]⟩
      ]⟩,
    ⟨[4, 6, 4, 6], [5, 7, 5, 7], .contexts [
        ⟨50, false, false, [], [6, 4, 6]⟩,
        ⟨63, false, false, [5], [4, 6]⟩,
        ⟨50, false, false, [5, 7], [6]⟩,
        ⟨63, false, false, [5, 7, 5], []⟩
      ]⟩,
    ⟨[77357, 5], [77357, 5], .contexts []⟩,
    ⟨[11, 77357], [11, 77357], .contexts []⟩,
    ⟨[11, 77357], [11, 77357], .contexts []⟩,
    ⟨[7, 11], [10, 6], .contexts [
        ⟨985, false, false, [], [10, 6]⟩
      ]⟩,
    ⟨[10, 6], [11, 7], .contexts [
        ⟨91, false, false, [], [6]⟩,
        ⟨63, false, false, [11], []⟩
      ]⟩,
    ⟨[1, 77357], [1, 77357], .contexts []⟩,
    ⟨[1, 77357], [1, 77357], .contexts []⟩,
    ⟨[7, 13], [12, 6], .contexts [
        ⟨934, false, false, [], [12, 6]⟩
      ]⟩,
    ⟨[12, 6], [13, 7], .contexts [
        ⟨108, false, false, [], [6]⟩,
        ⟨63, false, false, [13], []⟩
      ]⟩,
    ⟨[77357, 13], [77357, 13], .contexts []⟩,
    ⟨[13, 77357], [13, 77357], .contexts []⟩,
    ⟨[13, 77357], [13, 77357], .contexts []⟩,
    ⟨[7, 15, 7, 15], [], .contexts [
        ⟨60, false, false, [], []⟩
      ]⟩,
    ⟨[7, 15], [14, 6], .contexts [
        ⟨1790, false, false, [], [14, 6]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 028. -/
def y322TCContextRaw028 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[14, 6], [15, 7], .contexts [
        ⟨20, false, false, [], [6]⟩,
        ⟨63, false, false, [15], []⟩
      ]⟩,
    ⟨[77357, 15], [77357, 15], .contexts []⟩,
    ⟨[77359], [77357, 9], .source 38744⟩,
    ⟨[77357, 9], [77359], .contexts [
        ⟨1794, true, false, [], []⟩
      ]⟩,
    ⟨[77359], [77359], .contexts []⟩,
    ⟨[77357, 9], [77359], .contexts [
        ⟨1795, false, false, [], []⟩,
        ⟨1796, false, false, [], []⟩,
        ⟨1796, false, false, [], []⟩
      ]⟩,
    ⟨[5, 77359], [5, 77359], .contexts []⟩,
    ⟨[5, 77359], [5, 77359], .contexts []⟩,
    ⟨[77359, 3], [77359, 3], .contexts []⟩,
    ⟨[77359, 3], [5, 77359], .contexts [
        ⟨1800, false, false, [], []⟩,
        ⟨1797, true, false, [], [3]⟩,
        ⟨306, false, false, [77357], []⟩,
        ⟨307, false, false, [77357], []⟩,
        ⟨1771, false, false, [], [9]⟩,
        ⟨1771, false, false, [], [9]⟩,
        ⟨1763, true, false, [], [3, 9]⟩,
        ⟨1769, false, false, [77107], [9]⟩,
        ⟨1770, false, false, [77107], [9]⟩,
        ⟨301, false, false, [], [7, 9]⟩,
        ⟨1760, false, false, [5], [9]⟩,
        ⟨1767, false, false, [], [9]⟩,
        ⟨1768, false, false, [], [9]⟩,
        ⟨1766, false, false, [5], [9]⟩,
        ⟨53, true, false, [], [77357, 9]⟩,
        ⟨1767, false, false, [], [9]⟩,
        ⟨1768, false, false, [], [9]⟩,
        ⟨1768, false, false, [], [9]⟩,
        ⟨1795, false, false, [5], []⟩,
        ⟨1798, false, false, [], []⟩,
        ⟨1799, false, false, [], []⟩
      ]⟩,
    ⟨[77359], [77359], .contexts []⟩,
    ⟨[7, 77359], [7, 77359], .contexts []⟩,
    ⟨[7, 77359], [7, 77359], .contexts []⟩,
    ⟨[9, 5], [4, 8], .contexts [
        ⟨802, false, false, [], [4, 8]⟩
      ]⟩,
    ⟨[4, 8], [5, 9], .contexts [
        ⟨50, false, false, [], [8]⟩,
        ⟨77, false, false, [5], []⟩
      ]⟩,
    ⟨[77359, 5], [7, 77359], .contexts [
        ⟨1797, true, false, [], [5]⟩,
        ⟨1805, false, false, [77357], []⟩,
        ⟨1806, false, false, [77357], []⟩,
        ⟨1778, false, false, [], [9]⟩,
        ⟨1778, false, false, [], [9]⟩,
        ⟨1763, true, false, [], [5, 9]⟩,
        ⟨1776, false, false, [77107], [9]⟩,
        ⟨1777, false, false, [77107], [9]⟩,
        ⟨1772, false, false, [], [7, 9]⟩,
        ⟨1760, false, false, [7], [9]⟩,
        ⟨1773, false, false, [], [9]⟩,
        ⟨1774, false, false, [], [9]⟩,
        ⟨1766, false, false, [7], [9]⟩,
        ⟨66, true, false, [], [77357, 9]⟩,
        ⟨1773, false, false, [], [9]⟩,
        ⟨1774, false, false, [], [9]⟩,
        ⟨1774, false, false, [], [9]⟩,
        ⟨1795, false, false, [7], []⟩,
        ⟨1803, false, false, [], []⟩,
        ⟨1804, false, false, [], []⟩
      ]⟩,
    ⟨[77359, 5], [77359, 5], .contexts []⟩,
    ⟨[9, 7], [6, 8], .contexts [
        ⟨819, false, false, [], [6, 8]⟩
      ]⟩,
    ⟨[6, 8], [7, 9], .contexts [
        ⟨63, false, false, [], [8]⟩,
        ⟨77, false, false, [7], []⟩
      ]⟩,
    ⟨[77359, 7], [77359, 7], .contexts []⟩,
    ⟨[77359, 7], [77109], .contexts [
        ⟨1811, false, false, [], []⟩,
        ⟨1797, true, false, [], [7]⟩,
        ⟨1809, false, false, [77357], []⟩,
        ⟨1810, false, false, [77357], []⟩,
        ⟨1760, true, false, [], [7, 9]⟩,
        ⟨62, false, false, [77107], [9]⟩,
        ⟨253, false, false, [], [9]⟩,
        ⟨252, false, false, [], [9]⟩,
        ⟨253, false, false, [], [9]⟩,
        ⟨253, false, false, [], [9]⟩,
        ⟨297, false, false, [], []⟩,
        ⟨298, false, false, [], []⟩,
        ⟨299, false, false, [], []⟩,
        ⟨299, false, false, [], []⟩,
        ⟨309, false, false, [], []⟩,
        ⟨1118, true, false, [], [77109]⟩
      ]⟩,
    ⟨[1, 77359], [1, 77359], .contexts []⟩,
    ⟨[1, 77359], [1, 77359], .contexts []⟩,
    ⟨[77359, 13], [77359, 13], .contexts []⟩,
    ⟨[77359, 13], [1, 77359], .contexts [
        ⟨1815, false, false, [], []⟩,
        ⟨1797, true, false, [], [13]⟩,
        ⟨315, false, false, [77357], []⟩,
        ⟨316, false, false, [77357], []⟩,
        ⟨1787, false, false, [], [9]⟩,
        ⟨1787, false, false, [], [9]⟩,
        ⟨1763, true, false, [], [13, 9]⟩,
        ⟨1785, false, false, [77107], [9]⟩,
        ⟨1786, false, false, [77107], [9]⟩,
        ⟨310, false, false, [], [7, 9]⟩,
        ⟨1760, false, false, [1], [9]⟩,
        ⟨1783, false, false, [], [9]⟩,
        ⟨1784, false, false, [], [9]⟩,
        ⟨1766, false, false, [1], [9]⟩,
        ⟨25, true, false, [], [77357, 9]⟩,
        ⟨1783, false, false, [], [9]⟩,
        ⟨1784, false, false, [], [9]⟩,
        ⟨1784, false, false, [], [9]⟩,
        ⟨1795, false, false, [1], []⟩,
        ⟨1813, false, false, [], []⟩,
        ⟨1814, false, false, [], []⟩
      ]⟩,
    ⟨[77359, 13], [1, 77359], .contexts [
        ⟨1816, false, false, [], []⟩,
        ⟨1802, false, false, [1], []⟩,
        ⟨25, true, false, [], [77359]⟩
      ]⟩,
    ⟨[77359, 15], [13, 77359], .contexts [
        ⟨1797, true, false, [], [15]⟩,
        ⟨323, false, false, [77357], []⟩,
        ⟨324, false, false, [77357], []⟩,
        ⟨1793, false, false, [], [9]⟩,
        ⟨1793, false, false, [], [9]⟩,
        ⟨1763, true, false, [], [15, 9]⟩,
        ⟨1791, false, false, [77107], [9]⟩,
        ⟨1792, false, false, [77107], [9]⟩,
        ⟨319, false, false, [], [7, 9]⟩,
        ⟨1760, false, false, [13], [9]⟩,
        ⟨1788, false, false, [], [9]⟩,
        ⟨1789, false, false, [], [9]⟩,
        ⟨1766, false, false, [13], [9]⟩,
        ⟨153, true, false, [], [77357, 9]⟩,
        ⟨1788, false, false, [], [9]⟩,
        ⟨1789, false, false, [], [9]⟩,
        ⟨1789, false, false, [], [9]⟩,
        ⟨1795, false, false, [13], []⟩
      ]⟩,
    ⟨[77361], [77235, 1], .source 38745⟩,
    ⟨[77235, 1], [77361], .contexts [
        ⟨1819, true, false, [], []⟩
      ]⟩,
    ⟨[77361, 1], [77235], .contexts [
        ⟨1820, true, false, [], [1]⟩,
        ⟨18, false, false, [77235], []⟩,
        ⟨1105, false, false, [], []⟩
      ]⟩,
    ⟨[77361], [77361], .contexts []⟩,
    ⟨[77235, 1], [77361], .contexts [
        ⟨1820, false, false, [], []⟩,
        ⟨1822, false, false, [], []⟩,
        ⟨1822, false, false, [], []⟩
      ]⟩,
    ⟨[1, 3], [2, 0, 2, 0], .contexts [
        ⟨851, false, false, [], [2, 0, 2, 0]⟩
      ]⟩,
    ⟨[2, 0, 2], [3, 1, 3], .contexts [
        ⟨853, false, false, [], [2]⟩,
        ⟨36, false, false, [3, 1], []⟩
      ]⟩,
    ⟨[2, 0, 2, 0], [3, 1, 3, 1], .contexts [
        ⟨1825, false, false, [], [0]⟩,
        ⟨19, false, false, [3, 1, 3], []⟩
      ]⟩,
    ⟨[77361], [77361], .contexts []⟩,
    ⟨[77361, 3], [87, 77361], .contexts [
        ⟨1823, true, false, [], [3]⟩,
        ⟨1824, false, false, [77235], []⟩,
        ⟨1826, false, false, [77235], []⟩,
        ⟨1104, false, false, [], [1, 3, 1]⟩,
        ⟨1075, false, false, [], [1, 3, 1]⟩,
        ⟨1076, false, false, [], [1, 3, 1]⟩,
        ⟨1076, false, false, [], [1, 3, 1]⟩,
        ⟨1082, false, false, [], [3, 1]⟩,
        ⟨1078, false, false, [], [3, 1]⟩,
        ⟨1079, false, false, [], [3, 1]⟩,
        ⟨1079, false, false, [], [3, 1]⟩,
        ⟨1103, false, false, [87], [1]⟩,
        ⟨1820, false, false, [87], []⟩,
        ⟨1827, false, false, [87], []⟩
      ]⟩,
    ⟨[77361, 5], [111, 77113], .contexts [
        ⟨1823, true, false, [], [5]⟩,
        ⟨165, false, false, [77235], []⟩,
        ⟨166, false, false, [77235], []⟩,
        ⟨1129, false, false, [], [1]⟩,
        ⟨1125, false, false, [], [1]⟩,
        ⟨1126, false, false, [], [1]⟩,
        ⟨1126, false, false, [], [1]⟩,
        ⟨363, false, false, [111], []⟩,
        ⟨371, false, false, [111], []⟩,
        ⟨24, true, false, [], [111, 77113]⟩
      ]⟩,
    ⟨[77361, 11], [77361, 11], .contexts []⟩,
    ⟨[77361, 11], [109, 77221], .contexts [
        ⟨1830, false, false, [], []⟩,
        ⟨1823, true, false, [], [11]⟩,
        ⟨181, false, false, [77235], []⟩,
        ⟨182, false, false, [77235], []⟩,
        ⟨1124, false, false, [], [1]⟩,
        ⟨627, false, false, [], []⟩,
        ⟨917, false, false, [], []⟩,
        ⟨910, false, false, [], []⟩,
        ⟨910, false, false, [], []⟩,
        ⟨902, false, false, [109], []⟩,
        ⟨877, true, false, [], [77221]⟩
      ]⟩,
    ⟨[77221, 11], [107, 77361], .contexts [
        ⟨1831, true, false, [108], [11]⟩,
        ⟨90, false, false, [108, 77361], []⟩,
        ⟨913, true, false, [], [77361]⟩
      ]⟩,
    ⟨[77235, 15, 1], [109, 77361], .contexts [
        ⟨1123, false, false, [], [1]⟩,
        ⟨1123, false, false, [], [1]⟩,
        ⟨1106, true, false, [], [15, 1]⟩,
        ⟨245, false, false, [77233], [1]⟩,
        ⟨246, false, false, [77233], [1]⟩,
        ⟨1100, false, false, [], [3, 1]⟩,
        ⟨1101, false, false, [], [3, 1]⟩,
        ⟨1098, false, false, [], [3, 1]⟩,
        ⟨1099, false, false, [], [3, 1]⟩,
        ⟨1099, false, false, [], [3, 1]⟩,
        ⟨1103, false, false, [109], [1]⟩,
        ⟨1121, false, false, [], [1]⟩,
        ⟨1122, false, false, [], [1]⟩,
        ⟨1111, false, false, [109], [1]⟩,
        ⟨877, true, false, [], [77235, 1]⟩,
        ⟨1121, false, false, [], [1]⟩,
        ⟨1122, false, false, [], [1]⟩,
        ⟨1122, false, false, [], [1]⟩,
        ⟨1820, false, false, [109], []⟩
      ]⟩,
    ⟨[77361, 15], [109, 77361], .contexts [
        ⟨1823, true, false, [], [15]⟩,
        ⟨199, false, false, [77235], []⟩,
        ⟨200, false, false, [77235], []⟩,
        ⟨1833, false, false, [], []⟩,
        ⟨1827, false, false, [109], []⟩,
        ⟨877, true, false, [], [77361]⟩
      ]⟩,
    ⟨[285], [109, 135], .source 207⟩,
    ⟨[11, 13, 11, 13], [], .contexts [
        ⟨351, false, false, [], []⟩
      ]⟩,
    ⟨[77215, 13], [77215, 13], .contexts []⟩,
    ⟨[287], [284], .source 208⟩,
    ⟨[284], [284], .contexts []⟩,
    ⟨[77215, 13], [287, 77361], .contexts [
        ⟨1837, false, false, [], []⟩,
        ⟨597, true, false, [], [13]⟩,
        ⟨1835, false, false, [284], [77217, 11, 13]⟩,
        ⟨954, true, false, [284, 109], [11, 13]⟩,
        ⟨604, true, false, [284, 109], [11, 13]⟩,
        ⟨910, true, false, [284], [13, 11, 13]⟩,
        ⟨910, true, false, [284], [13, 11, 13]⟩,
        ⟨909, true, false, [284], [13, 11, 13]⟩,
        ⟨1831, true, false, [284], [13, 11, 13]⟩,
        ⟨1830, true, false, [284], [13, 11, 13]⟩,
        ⟨1836, false, false, [284, 77361], []⟩,
        ⟨1827, false, false, [284], []⟩,
        ⟨1839, true, false, [], [77361]⟩,
        ⟨1839, true, false, [], [77361]⟩,
        ⟨1838, true, false, [], [77361]⟩
      ]⟩,
    ⟨[77361, 13], [285, 77215], .contexts [
        ⟨1840, true, false, [286], [13]⟩,
        ⟨98, false, false, [286, 77215], []⟩,
        ⟨1838, false, true, [], [77215]⟩
      ]⟩,
    ⟨[287, 77361], [287, 77361], .contexts []⟩,
    ⟨[289], [287, 111], .source 209⟩,
    ⟨[289, 77115], [289, 77115], .contexts []⟩,
    ⟨[289, 77115], [289, 77115], .contexts []⟩,
    ⟨[13, 5, 13, 5], [], .contexts [
        ⟨115, false, false, [], []⟩
      ]⟩,
    ⟨[77115, 5], [77115, 5], .contexts []⟩,
    ⟨[291], [288], .source 210⟩,
    ⟨[288], [288], .contexts []⟩,
    ⟨[77115, 5], [291, 77215], .contexts [
        ⟨1847, false, false, [], []⟩,
        ⟨1845, true, false, [288], [5]⟩,
        ⟨1844, true, false, [288], [5]⟩,
        ⟨374, true, false, [], [5]⟩,
        ⟨1843, false, false, [288], [77113, 13, 5]⟩,
        ⟨1829, true, false, [288, 287], [13, 5]⟩,
        ⟨1842, true, false, [288], [5, 13, 5]⟩,
        ⟨1842, true, false, [288], [5, 13, 5]⟩,
        ⟨1840, true, false, [288], [5, 13, 5]⟩,
        ⟨1837, true, false, [288], [5, 13, 5]⟩,
        ⟨1846, false, false, [288, 77215], []⟩,
        ⟨979, false, false, [288], []⟩,
        ⟨1849, true, false, [], [77215]⟩,
        ⟨1849, true, false, [], [77215]⟩,
        ⟨1848, true, false, [], [77215]⟩
      ]⟩,
    ⟨[289], [290], .contexts [
        ⟨1848, true, true, [], []⟩
      ]⟩,
    ⟨[291, 77215], [291, 77215], .contexts []⟩,
    ⟨[77213, 5], [77213, 5], .contexts []⟩,
    ⟨[293], [289, 245], .source 211⟩,
    ⟨[77213, 5], [293, 77241], .contexts [
        ⟨1853, false, false, [], []⟩,
        ⟨593, true, false, [], [5]⟩,
        ⟨1852, true, false, [290], [9, 5]⟩,
        ⟨1852, true, false, [290], [9, 5]⟩,
        ⟨1850, true, false, [290], [9, 5]⟩,
        ⟨1847, true, false, [290], [9, 5]⟩,
        ⟨1672, false, false, [290, 77115], []⟩,
        ⟨77, false, false, [290, 77115], []⟩,
        ⟨1631, false, false, [290], []⟩,
        ⟨1604, false, false, [290, 245], []⟩,
        ⟨1851, true, false, [], [245, 77241]⟩,
        ⟨1854, true, false, [], [77241]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 029. -/
def y322TCContextRaw029 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[295], [292], .source 212⟩,
    ⟨[293, 77241], [293, 77241], .contexts []⟩,
    ⟨[293, 77241], [293, 77241], .contexts []⟩,
    ⟨[77213, 5], [293, 77241], .contexts [
        ⟨1853, false, false, [], []⟩,
        ⟨1855, false, false, [], []⟩,
        ⟨1857, false, false, [], []⟩,
        ⟨1858, false, false, [], []⟩,
        ⟨1858, false, false, [], []⟩
      ]⟩,
    ⟨[77241, 1], [77241, 1], .contexts []⟩,
    ⟨[292], [292], .contexts []⟩,
    ⟨[295], [292], .contexts [
        ⟨1856, false, false, [], []⟩,
        ⟨1861, false, false, [], []⟩,
        ⟨1861, false, false, [], []⟩
      ]⟩,
    ⟨[77241, 1], [295, 77209], .contexts [
        ⟨1860, false, false, [], []⟩,
        ⟨1859, true, false, [292], [1]⟩,
        ⟨256, false, false, [292, 77213], []⟩,
        ⟨257, false, false, [292, 77213], []⟩,
        ⟨999, false, false, [292], [5]⟩,
        ⟨640, false, false, [292], []⟩,
        ⟨641, false, false, [292], []⟩,
        ⟨584, false, false, [292], []⟩,
        ⟨584, false, false, [292], []⟩,
        ⟨1031, false, false, [292], []⟩,
        ⟨1862, true, false, [], [77209]⟩
      ]⟩,
    ⟨[293], [294], .contexts [
        ⟨1856, true, true, [], []⟩
      ]⟩,
    ⟨[295, 77209], [295, 77209], .contexts []⟩,
    ⟨[295, 77209], [295, 77209], .contexts []⟩,
    ⟨[77241, 1], [295, 77209], .contexts [
        ⟨1860, false, false, [], []⟩,
        ⟨1863, false, false, [], []⟩,
        ⟨1865, false, false, [], []⟩,
        ⟨1866, false, false, [], []⟩,
        ⟨1866, false, false, [], []⟩
      ]⟩,
    ⟨[297], [243, 29], .source 213⟩,
    ⟨[299], [297, 245], .source 214⟩,
    ⟨[301], [299, 295], .source 215⟩,
    ⟨[77209, 13], [77209, 13], .contexts []⟩,
    ⟨[293], [294], .contexts [
        ⟨1864, false, false, [], []⟩
      ]⟩,
    ⟨[303], [293, 301], .source 216⟩,
    ⟨[77209, 13], [303, 77209], .contexts [
        ⟨1871, false, false, [], []⟩,
        ⟨1867, true, false, [294], [13]⟩,
        ⟨189, false, false, [294, 77241], []⟩,
        ⟨192, false, false, [294, 77241], []⟩,
        ⟨1177, false, false, [294], [1, 13, 1]⟩,
        ⟨1609, false, false, [294], [1, 13, 1]⟩,
        ⟨1546, false, false, [294], [1, 13, 1]⟩,
        ⟨1546, false, false, [294], [1, 13, 1]⟩,
        ⟨1149, false, false, [294, 243], [13, 1]⟩,
        ⟨744, true, false, [294, 243], [77237, 13, 1]⟩,
        ⟨1868, true, false, [294], [77237, 13, 1]⟩,
        ⟨1550, false, false, [294, 297], [1]⟩,
        ⟨1869, true, false, [294], [77241, 1]⟩,
        ⟨1863, false, false, [294, 299], []⟩,
        ⟨1870, true, false, [294], [77209]⟩,
        ⟨1031, false, false, [294, 301], []⟩,
        ⟨1872, true, false, [], [301, 77209]⟩,
        ⟨1873, true, false, [], [77209]⟩
      ]⟩,
    ⟨[77209, 15], [77209, 15], .contexts []⟩,
    ⟨[294], [294], .contexts []⟩,
    ⟨[293], [294], .contexts [
        ⟨1872, false, false, [], []⟩,
        ⟨1876, false, false, [], []⟩,
        ⟨1876, false, false, [], []⟩
      ]⟩,
    ⟨[77209, 15], [293, 77245], .contexts [
        ⟨1875, false, false, [], []⟩,
        ⟨1867, true, false, [294], [15]⟩,
        ⟨199, false, false, [294, 77241], []⟩,
        ⟨200, false, false, [294, 77241], []⟩,
        ⟨1175, false, false, [294], [1]⟩,
        ⟨1658, false, false, [294], []⟩,
        ⟨1426, false, false, [294], []⟩,
        ⟨1187, false, false, [294], []⟩,
        ⟨1187, false, false, [294], []⟩,
        ⟨1663, false, false, [294], []⟩,
        ⟨1877, true, false, [], [77245]⟩
      ]⟩,
    ⟨[303, 77209], [303, 77209], .contexts []⟩,
    ⟨[77209, 13], [303, 77209], .contexts [
        ⟨1871, false, false, [], []⟩,
        ⟨1874, false, false, [], []⟩,
        ⟨1879, false, false, [], []⟩,
        ⟨1879, false, false, [], []⟩
      ]⟩,
    ⟨[13, 3, 13], [2], .contexts [
        ⟨106, false, false, [], [2]⟩
      ]⟩,
    ⟨[305], [302], .source 217⟩,
    ⟨[302], [302], .contexts []⟩,
    ⟨[305], [302], .contexts [
        ⟨1882, false, false, [], []⟩,
        ⟨1883, false, false, [], []⟩,
        ⟨1883, false, false, [], []⟩
      ]⟩,
    ⟨[77207, 13], [305, 77207], .contexts [
        ⟨581, true, false, [], [13]⟩,
        ⟨1880, true, false, [302], [3, 13]⟩,
        ⟨1881, false, false, [302, 77209], []⟩,
        ⟨1041, false, false, [302], []⟩,
        ⟨1039, false, false, [302], []⟩,
        ⟨1043, false, false, [302], []⟩,
        ⟨1884, true, false, [], [77207]⟩
      ]⟩,
    ⟨[13, 5, 13], [4], .contexts [
        ⟨115, false, false, [], [4]⟩
      ]⟩,
    ⟨[293, 77245], [293, 77245], .contexts []⟩,
    ⟨[293, 77245], [293, 77245], .contexts []⟩,
    ⟨[293, 77245, 3], [293, 77247], .contexts [
        ⟨1186, false, false, [293], []⟩
      ]⟩,
    ⟨[293, 77247], [293, 77247], .contexts []⟩,
    ⟨[293, 77247], [293, 77247], .contexts []⟩,
    ⟨[293, 77247], [293, 77247], .contexts []⟩,
    ⟨[15, 3, 15], [2], .contexts [
        ⟨33, false, false, [], [2]⟩
      ]⟩,
    ⟨[77247, 15], [77247, 15], .contexts []⟩,
    ⟨[77247, 15], [295, 77207], .contexts [
        ⟨1894, false, false, [], []⟩,
        ⟨1892, true, false, [292], [15]⟩,
        ⟨1891, true, false, [292], [15]⟩,
        ⟨1890, true, false, [292], [15]⟩,
        ⟨1889, true, false, [292], [15]⟩,
        ⟨1888, true, false, [292], [3, 15]⟩,
        ⟨1888, true, false, [292], [3, 15]⟩,
        ⟨1887, true, false, [292], [3, 15]⟩,
        ⟨1878, true, false, [292], [3, 15]⟩,
        ⟨1875, true, false, [292], [3, 15]⟩,
        ⟨1893, false, false, [292, 77209], []⟩,
        ⟨1041, false, false, [292], []⟩,
        ⟨1039, false, false, [292], []⟩,
        ⟨1043, false, false, [292], []⟩,
        ⟨1862, true, false, [], [77207]⟩
      ]⟩,
    ⟨[77207, 15], [293, 77247], .contexts [
        ⟨1895, true, false, [294], [15]⟩,
        ⟨3, false, false, [294, 77247], []⟩,
        ⟨1864, true, false, [], [77247]⟩
      ]⟩,
    ⟨[295, 77207], [295, 77207], .contexts []⟩,
    ⟨[295, 77203], [295, 77203], .contexts []⟩,
    ⟨[295, 77203], [295, 77203], .contexts []⟩,
    ⟨[77203, 1], [77203, 1], .contexts []⟩,
    ⟨[77203, 1], [293, 77247], .contexts [
        ⟨1900, false, false, [], []⟩,
        ⟨1899, true, false, [294], [1]⟩,
        ⟨1898, true, false, [294], [1]⟩,
        ⟨574, true, false, [], [1]⟩,
        ⟨578, true, false, [], [15, 1]⟩,
        ⟨1897, true, false, [294], [1, 15, 1]⟩,
        ⟨1897, true, false, [294], [1, 15, 1]⟩,
        ⟨1895, true, false, [294], [1, 15, 1]⟩,
        ⟨1894, true, false, [294], [1, 15, 1]⟩,
        ⟨911, false, false, [294, 77247], []⟩,
        ⟨1681, false, false, [294], []⟩,
        ⟨1877, true, false, [], [77247]⟩
      ]⟩,
    ⟨[77247, 1], [295, 77203], .contexts [
        ⟨1901, true, false, [292], [1]⟩,
        ⟨18, false, false, [292, 77203], []⟩,
        ⟨1856, true, false, [], [77203]⟩
      ]⟩,
    ⟨[293, 77247, 5], [293, 77249], .contexts [
        ⟨1189, false, false, [293], []⟩
      ]⟩,
    ⟨[293, 77249], [293, 77249], .contexts []⟩,
    ⟨[293, 77249], [293, 77249], .contexts []⟩,
    ⟨[293, 77249], [293, 77249], .contexts []⟩,
    ⟨[293, 77251], [293, 77251], .contexts []⟩,
    ⟨[293, 77251], [293, 77251], .contexts []⟩,
    ⟨[1, 5, 1, 5], [], .contexts [
        ⟨164, false, false, [], []⟩
      ]⟩,
    ⟨[77251, 5], [295, 77203], .contexts [
        ⟨1908, true, false, [292], [5]⟩,
        ⟨1907, true, false, [292], [5]⟩,
        ⟨1192, true, false, [], [5]⟩,
        ⟨1906, true, false, [292], [1, 5]⟩,
        ⟨1905, true, false, [292], [1, 5]⟩,
        ⟨1904, true, false, [292], [1, 5]⟩,
        ⟨1903, true, false, [292], [1, 5]⟩,
        ⟨1892, true, false, [292], [5, 1, 5]⟩,
        ⟨1892, true, false, [292], [5, 1, 5]⟩,
        ⟨1890, true, false, [292], [5, 1, 5]⟩,
        ⟨1901, true, false, [292], [5, 1, 5]⟩,
        ⟨1900, true, false, [292], [5, 1, 5]⟩,
        ⟨1909, false, false, [292, 77203], []⟩,
        ⟨1056, false, false, [292], []⟩,
        ⟨1862, true, false, [], [77203]⟩
      ]⟩,
    ⟨[77203, 5], [293, 77251], .contexts [
        ⟨1910, true, false, [294], [5]⟩,
        ⟨49, false, false, [294, 77251], []⟩,
        ⟨1864, true, false, [], [77251]⟩
      ]⟩,
    ⟨[77363], [77215, 15], .source 38746⟩,
    ⟨[77215, 15], [77363], .contexts [
        ⟨1912, true, false, [], []⟩
      ]⟩,
    ⟨[77215, 15], [77363], .contexts [
        ⟨1913, false, false, [], []⟩
      ]⟩,
    ⟨[77363], [77363], .contexts []⟩,
    ⟨[77363], [77363], .contexts []⟩,
    ⟨[77215, 15], [77363], .contexts [
        ⟨1914, false, false, [], []⟩,
        ⟨1915, false, false, [], []⟩,
        ⟨1916, false, false, [], []⟩,
        ⟨1916, false, false, [], []⟩
      ]⟩,
    ⟨[135, 77363], [135, 77363], .contexts []⟩,
    ⟨[135, 77363], [135, 77363], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 030. -/
def y322TCContextRaw030 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77363], [77363], .contexts []⟩,
    ⟨[77363, 1], [135, 77363], .contexts [
        ⟨1917, true, false, [], [1]⟩,
        ⟨17, false, false, [77215], []⟩,
        ⟨21, false, false, [77215], []⟩,
        ⟨1021, false, false, [], [15]⟩,
        ⟨1913, false, false, [135], []⟩,
        ⟨1918, false, false, [], []⟩,
        ⟨1919, false, false, [], []⟩,
        ⟨1920, false, false, [135], []⟩,
        ⟨995, true, false, [], [77363]⟩
      ]⟩,
    ⟨[153, 77363], [153, 77363], .contexts []⟩,
    ⟨[153, 77363], [153, 77363], .contexts []⟩,
    ⟨[77363, 3], [77363, 3], .contexts []⟩,
    ⟨[77363, 3], [153, 77363], .contexts [
        ⟨1924, false, false, [], []⟩,
        ⟨1917, true, false, [], [3]⟩,
        ⟨34, false, false, [77215], []⟩,
        ⟨37, false, false, [77215], []⟩,
        ⟨1007, false, false, [], [15]⟩,
        ⟨1913, false, false, [153], []⟩,
        ⟨1922, false, false, [], []⟩,
        ⟨1923, false, false, [], []⟩,
        ⟨1920, false, false, [153], []⟩,
        ⟨24, true, false, [], [153, 77363]⟩
      ]⟩,
    ⟨[289, 77117], [289, 77117], .contexts []⟩,
    ⟨[289, 77117], [289, 77117], .contexts []⟩,
    ⟨[77363, 5], [77363, 5], .contexts []⟩,
    ⟨[77363, 5], [289, 77117], .contexts [
        ⟨1928, false, false, [], []⟩,
        ⟨1917, true, false, [], [5]⟩,
        ⟨48, false, false, [77215], []⟩,
        ⟨51, false, false, [77215], []⟩,
        ⟨1850, true, false, [290], [5, 15]⟩,
        ⟨49, false, false, [290, 77115], [15]⟩,
        ⟨1851, true, false, [], [77115, 15]⟩,
        ⟨1844, false, false, [], [15]⟩,
        ⟨1845, false, false, [], [15]⟩,
        ⟨1845, false, false, [], [15]⟩,
        ⟨395, false, false, [289], []⟩,
        ⟨1926, false, false, [], []⟩,
        ⟨1927, false, false, [], []⟩,
        ⟨402, false, false, [289], []⟩,
        ⟨24, true, false, [], [289, 77117]⟩
      ]⟩,
    ⟨[311], [153, 289], .source 220⟩,
    ⟨[3, 5, 3, 5, 3], [4], .contexts [
        ⟨1478, false, false, [], [4]⟩
      ]⟩,
    ⟨[311, 77121, 3], [289, 77117], .contexts [
        ⟨424, true, false, [311], [3]⟩,
        ⟨415, true, false, [311], [5, 3]⟩,
        ⟨1930, false, false, [], [77117, 3, 5, 3]⟩,
        ⟨1929, true, false, [153], [3, 5, 3]⟩,
        ⟨1923, true, false, [], [5, 3, 5, 3]⟩,
        ⟨1923, true, false, [], [5, 3, 5, 3]⟩,
        ⟨1922, true, false, [], [5, 3, 5, 3]⟩,
        ⟨1925, true, false, [], [5, 3, 5, 3]⟩,
        ⟨1924, true, false, [], [5, 3, 5, 3]⟩,
        ⟨1931, false, false, [77363], []⟩,
        ⟨50, false, false, [77363], []⟩,
        ⟨1928, false, false, [], []⟩,
        ⟨1929, false, false, [], []⟩,
        ⟨1926, false, false, [], []⟩,
        ⟨1927, false, false, [], []⟩,
        ⟨1927, false, false, [], []⟩
      ]⟩,
    ⟨[313], [310], .source 221⟩,
    ⟨[315], [313, 289], .source 222⟩,
    ⟨[317], [314], .source 223⟩,
    ⟨[317], [317], .contexts []⟩,
    ⟨[317], [317], .contexts []⟩,
    ⟨[317], [317], .contexts []⟩,
    ⟨[315], [316], .contexts [
        ⟨1935, true, true, [], []⟩
      ]⟩,
    ⟨[77121], [315, 77119], .contexts [
        ⟨1936, false, false, [316], [77121]⟩,
        ⟨1937, false, false, [316], [77121]⟩,
        ⟨1938, false, false, [316], [77121]⟩,
        ⟨1935, false, false, [316], [77121]⟩,
        ⟨35, true, false, [316, 314, 77121], []⟩,
        ⟨1932, false, false, [316, 314, 310], [3]⟩,
        ⟨402, false, false, [316, 314, 310, 289], [3]⟩,
        ⟨1933, true, false, [316, 314], [289, 77117, 3]⟩,
        ⟨1934, true, false, [316, 314], [77117, 3]⟩,
        ⟨418, false, false, [316], []⟩,
        ⟨1939, true, false, [], [77119]⟩
      ]⟩,
    ⟨[315, 77119], [315, 77119], .contexts []⟩,
    ⟨[77121], [315, 77119], .contexts [
        ⟨1940, false, false, [], []⟩,
        ⟨1941, false, false, [], []⟩
      ]⟩,
    ⟨[317], [314], .contexts [
        ⟨1935, false, false, [], []⟩
      ]⟩,
    ⟨[314], [314], .contexts []⟩,
    ⟨[77119, 1], [317, 77123], .contexts [
        ⟨1940, true, false, [314], [1]⟩,
        ⟨428, false, false, [314], []⟩,
        ⟨728, false, false, [314], []⟩,
        ⟨1944, true, false, [], [77123]⟩,
        ⟨1944, true, false, [], [77123]⟩,
        ⟨1943, true, false, [], [77123]⟩
      ]⟩,
    ⟨[77119, 3], [77117], .contexts [
        ⟨731, false, false, [], []⟩,
        ⟨397, false, false, [], []⟩,
        ⟨398, false, false, [], []⟩,
        ⟨398, false, false, [], []⟩
      ]⟩,
    ⟨[319], [19, 317], .source 224⟩,
    ⟨[317, 77123], [317, 77123], .contexts []⟩,
    ⟨[317, 77123], [317, 77123], .contexts []⟩,
    ⟨[77119, 1], [317, 77123], .contexts [
        ⟨1945, false, false, [], []⟩,
        ⟨1948, false, false, [], []⟩,
        ⟨1949, false, false, [], []⟩,
        ⟨1949, false, false, [], []⟩
      ]⟩,
    ⟨[3, 1, 3, 1, 3], [0], .contexts [
        ⟨212, false, false, [], [0]⟩
      ]⟩,
    ⟨[77119, 0], [77119, 1], .contexts [
        ⟨19, false, false, [77119], []⟩
      ]⟩,
    ⟨[77123, 3], [77123, 3], .contexts []⟩,
    ⟨[77123], [77123], .contexts []⟩,
    ⟨[321], [318], .source 225⟩,
    ⟨[323], [321, 317], .source 226⟩,
    ⟨[77123, 3], [323, 77123], .contexts [
        ⟨1953, false, false, [], []⟩,
        ⟨1947, false, false, [318], [77123, 3]⟩,
        ⟨735, false, false, [318], [317, 77123, 3]⟩,
        ⟨1945, true, false, [318, 1], [3]⟩,
        ⟨415, true, false, [318, 1], [1, 3]⟩,
        ⟨401, true, false, [318], [3, 1, 3]⟩,
        ⟨401, true, false, [318], [3, 1, 3]⟩,
        ⟨400, true, false, [318], [3, 1, 3]⟩,
        ⟨732, true, false, [318], [3, 1, 3]⟩,
        ⟨1946, true, false, [318], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [318, 77119], []⟩,
        ⟨1952, false, false, [318], []⟩,
        ⟨1950, false, false, [318], []⟩,
        ⟨1954, false, false, [318, 317], []⟩,
        ⟨1955, true, false, [], [317, 77123]⟩,
        ⟨1956, true, false, [], [77123]⟩
      ]⟩,
    ⟨[77121], [315, 77119], .contexts [
        ⟨1942, false, false, [], []⟩
      ]⟩,
    ⟨[77119, 5], [315, 77119], .contexts [
        ⟨424, false, false, [], []⟩,
        ⟨1958, false, false, [], []⟩,
        ⟨1941, false, false, [], []⟩,
        ⟨1941, false, false, [], []⟩
      ]⟩,
    ⟨[77123, 5], [77123, 5], .contexts []⟩,
    ⟨[317], [317], .contexts [
        ⟨24, false, false, [], [317]⟩,
        ⟨1937, false, false, [], []⟩,
        ⟨1938, false, false, [], []⟩
      ]⟩,
    ⟨[77123, 5], [317, 77123], .contexts [
        ⟨1960, false, false, [], []⟩,
        ⟨1935, true, false, [315], [77123, 5]⟩,
        ⟨1945, true, false, [315], [5]⟩,
        ⟨1959, true, false, [], [1, 5]⟩,
        ⟨1509, false, false, [77119], []⟩,
        ⟨1952, false, false, [], []⟩,
        ⟨1950, false, false, [], []⟩,
        ⟨1954, false, false, [317], []⟩,
        ⟨1961, true, false, [], [77123]⟩
      ]⟩,
    ⟨[323, 77123], [323, 77123], .contexts []⟩,
    ⟨[77123, 3], [323, 77123], .contexts [
        ⟨1953, false, false, [], []⟩,
        ⟨1957, false, false, [], []⟩,
        ⟨1963, false, false, [], []⟩,
        ⟨1963, false, false, [], []⟩
      ]⟩,
    ⟨[77123, 9], [77125], .contexts [
        ⟨431, false, false, [], []⟩
      ]⟩,
    ⟨[77123, 9], [77125], .contexts [
        ⟨1965, false, false, [], []⟩,
        ⟨726, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩
      ]⟩,
    ⟨[77123, 8], [77123, 9], .contexts [
        ⟨77, false, false, [77123], []⟩
      ]⟩,
    ⟨[77125, 3], [77125, 3], .contexts []⟩,
    ⟨[77125], [77125], .contexts []⟩,
    ⟨[325], [322], .source 227⟩,
    ⟨[322], [322], .contexts []⟩,
    ⟨[77125, 3], [325, 77125], .contexts [
        ⟨1968, false, false, [], []⟩,
        ⟨431, true, false, [], [3]⟩,
        ⟨1964, true, false, [322], [9, 3]⟩,
        ⟨1010, false, false, [322, 77123], []⟩,
        ⟨1967, false, false, [322], []⟩,
        ⟨1966, false, false, [322], []⟩,
        ⟨1969, false, false, [322], []⟩,
        ⟨1971, true, false, [], [77125]⟩,
        ⟨1971, true, false, [], [77125]⟩,
        ⟨1970, true, false, [], [77125]⟩
      ]⟩,
    ⟨[77125, 5], [77125, 5], .contexts []⟩,
    ⟨[316], [316], .contexts []⟩,
    ⟨[315], [316], .contexts [
        ⟨1939, false, false, [], []⟩,
        ⟨1974, false, false, [], []⟩,
        ⟨1974, false, false, [], []⟩
      ]⟩,
    ⟨[77125, 5], [315, 77125], .contexts [
        ⟨1973, false, false, [], []⟩,
        ⟨431, true, false, [], [5]⟩,
        ⟨1949, true, false, [316], [9, 5]⟩,
        ⟨1949, true, false, [316], [9, 5]⟩,
        ⟨1948, true, false, [316], [9, 5]⟩,
        ⟨1962, true, false, [316], [9, 5]⟩,
        ⟨1960, true, false, [316], [9, 5]⟩,
        ⟨1672, false, false, [316, 77123], []⟩,
        ⟨1967, false, false, [316], []⟩,
        ⟨1966, false, false, [316], []⟩,
        ⟨1969, false, false, [316], []⟩,
        ⟨1975, true, false, [], [77125]⟩
      ]⟩,
    ⟨[325, 77125], [325, 77125], .contexts []⟩,
    ⟨[77125, 11], [77127], .contexts [
        ⟨434, false, false, [], []⟩
      ]⟩,
    ⟨[77125, 11], [77127], .contexts [
        ⟨1978, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩
      ]⟩,
    ⟨[77125, 10], [77125, 11], .contexts [
        ⟨91, false, false, [77125], []⟩
      ]⟩,
    ⟨[77127, 3], [77127, 3], .contexts []⟩,
    ⟨[77127], [77127], .contexts []⟩,
    ⟨[324], [324], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 031. -/
def y322TCContextRaw031 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77127, 3], [323, 77127], .contexts [
        ⟨1981, false, false, [], []⟩,
        ⟨434, true, false, [], [3]⟩,
        ⟨1977, true, false, [324], [11, 3]⟩,
        ⟨1977, true, false, [324], [11, 3]⟩,
        ⟨1972, true, false, [324], [11, 3]⟩,
        ⟨1968, true, false, [324], [11, 3]⟩,
        ⟨976, false, false, [324, 77125], []⟩,
        ⟨1980, false, false, [324], []⟩,
        ⟨1979, false, false, [324], []⟩,
        ⟨1982, false, false, [324], []⟩,
        ⟨1983, true, false, [], [77127]⟩,
        ⟨1983, true, false, [], [77127]⟩,
        ⟨1970, false, true, [], [77127]⟩
      ]⟩,
    ⟨[315, 77125], [315, 77125], .contexts []⟩,
    ⟨[77125, 5], [315, 77125], .contexts [
        ⟨1973, false, false, [], []⟩,
        ⟨1976, false, false, [], []⟩,
        ⟨1985, false, false, [], []⟩,
        ⟨1985, false, false, [], []⟩
      ]⟩,
    ⟨[77127, 5], [77127, 5], .contexts []⟩,
    ⟨[317], [314], .contexts [
        ⟨1936, false, false, [], []⟩,
        ⟨1943, false, false, [], []⟩,
        ⟨1944, false, false, [], []⟩,
        ⟨1944, false, false, [], []⟩
      ]⟩,
    ⟨[77127, 5], [317, 77127], .contexts [
        ⟨1987, false, false, [], []⟩,
        ⟨434, true, false, [], [5]⟩,
        ⟨1986, true, false, [314], [11, 5]⟩,
        ⟨1645, false, false, [314, 77125], []⟩,
        ⟨1980, false, false, [314], []⟩,
        ⟨1979, false, false, [314], []⟩,
        ⟨1982, false, false, [314], []⟩,
        ⟨1988, true, false, [], [77127]⟩
      ]⟩,
    ⟨[317, 77127], [317, 77127], .contexts []⟩,
    ⟨[77127, 5], [317, 77127], .contexts [
        ⟨1987, false, false, [], []⟩,
        ⟨1989, false, false, [], []⟩,
        ⟨1990, false, false, [], []⟩,
        ⟨1990, false, false, [], []⟩
      ]⟩,
    ⟨[77127, 1], [77129], .contexts [
        ⟨437, false, false, [], []⟩
      ]⟩,
    ⟨[77129, 5], [77129, 5], .contexts []⟩,
    ⟨[77129], [77129], .contexts []⟩,
    ⟨[77129, 5], [315, 77129], .contexts [
        ⟨1993, false, false, [], []⟩,
        ⟨437, true, false, [], [5]⟩,
        ⟨1991, true, false, [316], [1, 5]⟩,
        ⟨1509, false, false, [316, 77127], []⟩,
        ⟨19, false, false, [316, 77127], []⟩,
        ⟨1992, false, false, [316], []⟩,
        ⟨721, false, false, [316], []⟩,
        ⟨442, false, false, [316], []⟩,
        ⟨442, false, false, [316], []⟩,
        ⟨1994, false, false, [316], []⟩,
        ⟨1975, true, false, [], [77129]⟩
      ]⟩,
    ⟨[315, 77129], [315, 77129], .contexts []⟩,
    ⟨[77129, 13], [77131], .contexts [
        ⟨441, false, false, [], []⟩
      ]⟩,
    ⟨[77129, 13], [77131], .contexts [
        ⟨1997, false, false, [], []⟩,
        ⟨720, false, false, [], []⟩,
        ⟨446, false, false, [], []⟩,
        ⟨446, false, false, [], []⟩
      ]⟩,
    ⟨[77129, 12], [77129, 13], .contexts [
        ⟨108, false, false, [77129], []⟩
      ]⟩,
    ⟨[77131, 5], [77131, 5], .contexts []⟩,
    ⟨[77131], [77131], .contexts []⟩,
    ⟨[77131, 5], [317, 77131], .contexts [
        ⟨2000, false, false, [], []⟩,
        ⟨441, true, false, [], [5]⟩,
        ⟨1996, true, false, [314], [13, 5]⟩,
        ⟨1996, true, false, [314], [13, 5]⟩,
        ⟨1995, true, false, [314], [13, 5]⟩,
        ⟨1993, true, false, [314], [13, 5]⟩,
        ⟨1578, false, false, [314, 77129], []⟩,
        ⟨1999, false, false, [314], []⟩,
        ⟨1998, false, false, [314], []⟩,
        ⟨2001, false, false, [314], []⟩,
        ⟨1988, true, false, [], [77131]⟩
      ]⟩,
    ⟨[317, 77131], [317, 77131], .contexts []⟩,
    ⟨[77131, 15], [77133], .contexts [
        ⟨445, false, false, [], []⟩
      ]⟩,
    ⟨[77131, 15], [77133], .contexts [
        ⟨2004, false, false, [], []⟩,
        ⟨719, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩
      ]⟩,
    ⟨[5, 15, 5], [14], .contexts [
        ⟨289, false, false, [], [14]⟩
      ]⟩,
    ⟨[77131, 14], [77131, 15], .contexts [
        ⟨20, false, false, [77131], []⟩
      ]⟩,
    ⟨[77133, 5], [77133, 5], .contexts []⟩,
    ⟨[77133], [77133], .contexts []⟩,
    ⟨[77133, 5], [315, 77133], .contexts [
        ⟨2008, false, false, [], []⟩,
        ⟨445, true, false, [], [5]⟩,
        ⟨2003, true, false, [316], [15, 5]⟩,
        ⟨2003, true, false, [316], [15, 5]⟩,
        ⟨2002, true, false, [316], [15, 5]⟩,
        ⟨2000, true, false, [316], [15, 5]⟩,
        ⟨2006, false, false, [316, 77131], []⟩,
        ⟨2007, false, false, [316], []⟩,
        ⟨2005, false, false, [316], []⟩,
        ⟨2009, false, false, [316], []⟩,
        ⟨1975, true, false, [], [77133]⟩
      ]⟩,
    ⟨[315, 77133], [315, 77133], .contexts []⟩,
    ⟨[77135, 5], [77135, 5], .contexts []⟩,
    ⟨[77135], [77135], .contexts []⟩,
    ⟨[317, 77135], [317, 77135], .contexts []⟩,
    ⟨[77135, 5], [317, 77135], .contexts [
        ⟨2012, false, false, [], []⟩,
        ⟨2012, false, false, [], []⟩,
        ⟨448, true, false, [], [5]⟩,
        ⟨2011, true, false, [314], [1, 5]⟩,
        ⟨2011, true, false, [314], [1, 5]⟩,
        ⟨2010, true, false, [314], [1, 5]⟩,
        ⟨2008, true, false, [314], [1, 5]⟩,
        ⟨1509, false, false, [314, 77133], []⟩,
        ⟨19, false, false, [314, 77133], []⟩,
        ⟨448, false, false, [314], []⟩,
        ⟨717, false, false, [314], []⟩,
        ⟨453, false, false, [314], []⟩,
        ⟨453, false, false, [314], []⟩,
        ⟨2013, false, false, [314], []⟩,
        ⟨1988, true, false, [], [77135]⟩,
        ⟨2014, false, false, [], []⟩,
        ⟨2014, false, false, [], []⟩
      ]⟩,
    ⟨[77135, 3], [77137], .contexts [
        ⟨452, false, false, [], []⟩,
        ⟨715, false, false, [], []⟩,
        ⟨457, false, false, [], []⟩,
        ⟨457, false, false, [], []⟩
      ]⟩,
    ⟨[77137, 5], [77139], .contexts [
        ⟨456, false, false, [], []⟩
      ]⟩,
    ⟨[5, 3, 5, 3], [2, 4], .contexts [
        ⟨263, false, false, [], [2, 4]⟩
      ]⟩,
    ⟨[77139, 3], [77139, 3], .contexts []⟩,
    ⟨[77139], [77139], .contexts []⟩,
    ⟨[77139, 3], [315, 77139], .contexts [
        ⟨2019, false, false, [], []⟩,
        ⟨456, true, false, [], [3]⟩,
        ⟨452, true, false, [], [5, 3]⟩,
        ⟨2015, true, false, [316], [3, 5, 3]⟩,
        ⟨2018, false, false, [316, 77135], []⟩,
        ⟨265, false, false, [316, 77135], []⟩,
        ⟨2016, false, false, [316], [5]⟩,
        ⟨2017, false, false, [316], []⟩,
        ⟨712, false, false, [316], []⟩,
        ⟨460, false, false, [316], []⟩,
        ⟨460, false, false, [316], []⟩,
        ⟨2020, false, false, [316], []⟩,
        ⟨1975, true, false, [], [77139]⟩
      ]⟩,
    ⟨[77365], [77245, 13], .source 38747⟩,
    ⟨[77245, 13], [77365], .contexts [
        ⟨2022, true, false, [], []⟩
      ]⟩,
    ⟨[77365, 13], [77245], .contexts [
        ⟨2023, true, false, [], [13]⟩,
        ⟨98, false, false, [77245], []⟩,
        ⟨1187, false, false, [], []⟩
      ]⟩,
    ⟨[77365], [77365], .contexts []⟩,
    ⟨[77245, 13], [77365], .contexts [
        ⟨2023, false, false, [], []⟩,
        ⟨2025, false, false, [], []⟩,
        ⟨2025, false, false, [], []⟩
      ]⟩,
    ⟨[77245, 1, 13, 1, 13], [13, 77365], .contexts [
        ⟨1427, false, false, [], [13, 1, 13]⟩,
        ⟨1173, false, false, [], [13, 1, 13]⟩,
        ⟨1174, false, false, [], [13, 1, 13]⟩,
        ⟨1174, false, false, [], [13, 1, 13]⟩,
        ⟨1175, true, false, [], [13, 1, 13]⟩,
        ⟨408, false, false, [77241], [1, 13]⟩,
        ⟨410, false, false, [77241], [1, 13]⟩,
        ⟨1179, false, false, [], [1, 13]⟩,
        ⟨1180, false, false, [], [1, 13]⟩,
        ⟨1181, false, false, [13], [1, 13]⟩,
        ⟨153, true, false, [], [77243, 1, 13]⟩,
        ⟨1178, false, false, [], [1, 13]⟩,
        ⟨1180, false, false, [], [1, 13]⟩,
        ⟨1180, false, false, [], [1, 13]⟩,
        ⟨1183, false, false, [13], [13]⟩,
        ⟨2023, false, false, [13], []⟩
      ]⟩,
    ⟨[77365], [77365], .contexts []⟩,
    ⟨[77365, 1], [13, 77365], .contexts [
        ⟨2026, true, false, [], [1]⟩,
        ⟨387, false, false, [77245], []⟩,
        ⟨390, false, false, [77245], []⟩,
        ⟨2027, false, false, [], []⟩,
        ⟨2028, false, false, [13], []⟩,
        ⟨153, true, false, [], [77365]⟩
      ]⟩,
    ⟨[277, 77365], [277, 77365], .contexts []⟩,
    ⟨[277, 77365], [277, 77365], .contexts []⟩,
    ⟨[277, 77365], [277, 77365], .contexts []⟩,
    ⟨[77365, 9], [77365, 9], .contexts []⟩,
    ⟨[277], [277], .contexts [
        ⟨24, false, false, [], [277]⟩
      ]⟩,
    ⟨[77365, 9], [277, 77365], .contexts [
        ⟨2033, false, false, [], []⟩,
        ⟨2026, true, false, [], [9]⟩,
        ⟨130, false, false, [77245], []⟩,
        ⟨131, false, false, [77245], []⟩,
        ⟨1676, false, false, [], [13]⟩,
        ⟨2023, false, false, [277], []⟩,
        ⟨2030, false, false, [], []⟩,
        ⟨2031, false, false, [], []⟩,
        ⟨2032, false, false, [], []⟩,
        ⟨2028, false, false, [277], []⟩,
        ⟨2034, true, false, [], [77365]⟩
      ]⟩,
    ⟨[245, 77365], [245, 77365], .contexts []⟩,
    ⟨[245, 77365], [245, 77365], .contexts []⟩,
    ⟨[77365, 11], [77365, 11], .contexts []⟩,
    ⟨[77365, 11], [245, 77365], .contexts [
        ⟨2038, false, false, [], []⟩,
        ⟨2026, true, false, [], [11]⟩,
        ⟨137, false, false, [77245], []⟩,
        ⟨138, false, false, [77245], []⟩,
        ⟨1690, false, false, [], [13]⟩,
        ⟨2023, false, false, [245], []⟩,
        ⟨2036, false, false, [], []⟩,
        ⟨2037, false, false, [], []⟩,
        ⟨2028, false, false, [245], []⟩,
        ⟨1606, true, false, [], [77365]⟩
      ]⟩,
    ⟨[327], [295, 303], .source 228⟩,
    ⟨[329], [327, 293], .source 229⟩,
    ⟨[329, 77365], [329, 77365], .contexts []⟩,
    ⟨[329, 77365], [329, 77365], .contexts []⟩,
    ⟨[77245, 15, 13, 15, 13], [329, 77365], .contexts [
        ⟨1878, true, false, [292], [15, 13, 15, 13]⟩,
        ⟨3, false, false, [292, 77209], [13, 15, 13]⟩,
        ⟨1856, true, false, [], [77209, 13, 15, 13]⟩,
        ⟨1865, false, false, [], [13, 15, 13]⟩,
        ⟨1866, false, false, [], [13, 15, 13]⟩,
        ⟨1866, false, false, [], [13, 15, 13]⟩,
        ⟨1874, false, false, [295], [15, 13]⟩,
        ⟨2040, true, false, [], [77209, 15, 13]⟩,
        ⟨1878, false, false, [327], [13]⟩,
        ⟨2041, true, false, [], [77245, 13]⟩,
        ⟨2023, false, false, [329], []⟩,
        ⟨2042, false, false, [], []⟩,
        ⟨2043, false, false, [], []⟩
      ]⟩,
    ⟨[77365, 15], [77365, 15], .contexts []⟩,
    ⟨[329], [329], .contexts [
        ⟨24, false, false, [], [329]⟩
      ]⟩,
    ⟨[77365, 15], [329, 77365], .contexts [
        ⟨2045, false, false, [], []⟩,
        ⟨2026, true, false, [], [15]⟩,
        ⟨148, false, false, [77245], []⟩,
        ⟨150, false, false, [77245], []⟩,
        ⟨2044, false, false, [], []⟩,
        ⟨2028, false, false, [329], []⟩,
        ⟨2046, true, false, [], [77365]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 032. -/
def y322TCContextRaw032 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77367], [77365, 3], .source 38748⟩,
    ⟨[77365, 3], [77367], .contexts [
        ⟨2048, true, false, [], []⟩
      ]⟩,
    ⟨[77367], [77367], .contexts []⟩,
    ⟨[77367], [77367], .contexts []⟩,
    ⟨[77365, 3], [77367], .contexts [
        ⟨2049, false, false, [], []⟩,
        ⟨2050, false, false, [], []⟩,
        ⟨2051, false, false, [], []⟩,
        ⟨2051, false, false, [], []⟩
      ]⟩,
    ⟨[277, 77367], [277, 77367], .contexts []⟩,
    ⟨[277, 77367], [277, 77367], .contexts []⟩,
    ⟨[277, 77367], [277, 77367], .contexts []⟩,
    ⟨[77367, 9], [77367, 9], .contexts []⟩,
    ⟨[77367], [77367], .contexts []⟩,
    ⟨[245, 77367], [245, 77367], .contexts []⟩,
    ⟨[245, 77367], [245, 77367], .contexts []⟩,
    ⟨[77367, 11], [77367, 11], .contexts []⟩,
    ⟨[77367, 13], [77367, 13], .contexts []⟩,
    ⟨[77367, 13], [77247], .contexts [
        ⟨2061, false, false, [], []⟩,
        ⟨2052, true, false, [], [13]⟩,
        ⟨238, false, false, [77365], []⟩,
        ⟨239, false, false, [77365], []⟩,
        ⟨2024, false, false, [], [3]⟩,
        ⟨1426, false, false, [], [3]⟩,
        ⟨1187, false, false, [], [3]⟩,
        ⟨1187, false, false, [], [3]⟩,
        ⟨1677, false, false, [], []⟩,
        ⟨1425, false, false, [], []⟩,
        ⟨1190, false, false, [], []⟩,
        ⟨1190, false, false, [], []⟩,
        ⟨1681, false, false, [], []⟩,
        ⟨1118, true, false, [], [77247]⟩
      ]⟩,
    ⟨[329, 77367], [329, 77367], .contexts []⟩,
    ⟨[329, 77367], [329, 77367], .contexts []⟩,
    ⟨[77367, 15], [77367, 15], .contexts []⟩,
    ⟨[77369], [77367, 5], .source 38749⟩,
    ⟨[77367, 5], [77369], .contexts [
        ⟨2066, true, false, [], []⟩
      ]⟩,
    ⟨[77369, 5], [77367], .contexts [
        ⟨2067, true, false, [], [5]⟩,
        ⟨49, false, false, [77367], []⟩,
        ⟨2051, false, false, [], []⟩
      ]⟩,
    ⟨[77369], [77369], .contexts []⟩,
    ⟨[77369], [77369], .contexts []⟩,
    ⟨[77367, 5], [77369], .contexts [
        ⟨2067, false, false, [], []⟩,
        ⟨2069, false, false, [], []⟩,
        ⟨2070, false, false, [], []⟩,
        ⟨2070, false, false, [], []⟩
      ]⟩,
    ⟨[277, 77369], [277, 77369], .contexts []⟩,
    ⟨[277, 77369], [277, 77369], .contexts []⟩,
    ⟨[77367, 9, 5], [277, 77369], .contexts [
        ⟨2056, false, false, [], [5]⟩,
        ⟨2056, false, false, [], [5]⟩,
        ⟨2052, true, false, [], [9, 5]⟩,
        ⟨1112, false, false, [77365], [5]⟩,
        ⟨1113, false, false, [77365], [5]⟩,
        ⟨2033, false, false, [], [3, 5]⟩,
        ⟨2035, false, false, [], [3, 5]⟩,
        ⟨2030, false, false, [], [3, 5]⟩,
        ⟨2032, false, false, [], [3, 5]⟩,
        ⟨2032, false, false, [], [3, 5]⟩,
        ⟨2049, false, false, [277], [5]⟩,
        ⟨2053, false, false, [], [5]⟩,
        ⟨2054, false, false, [], [5]⟩,
        ⟨2055, false, false, [], [5]⟩,
        ⟨2057, false, false, [277], [5]⟩,
        ⟨2034, true, false, [], [77367, 5]⟩,
        ⟨2053, false, false, [], [5]⟩,
        ⟨2055, false, false, [], [5]⟩,
        ⟨2055, false, false, [], [5]⟩,
        ⟨2067, false, false, [277], []⟩,
        ⟨2072, false, false, [], []⟩,
        ⟨2073, false, false, [], []⟩
      ]⟩,
    ⟨[277, 77369], [277, 77369], .contexts []⟩,
    ⟨[5, 9], [8, 4], .contexts [
        ⟨1496, false, false, [], [8, 4]⟩
      ]⟩,
    ⟨[8, 4], [9, 5], .contexts [
        ⟨77, false, false, [], [4]⟩,
        ⟨50, false, false, [9], []⟩
      ]⟩,
    ⟨[77369], [77369], .contexts []⟩,
    ⟨[245, 77369], [245, 77369], .contexts []⟩,
    ⟨[77367, 11, 5], [245, 77369], .contexts [
        ⟨2060, false, false, [], [5]⟩,
        ⟨2060, false, false, [], [5]⟩,
        ⟨2052, true, false, [], [11, 5]⟩,
        ⟨231, false, false, [77365], [5]⟩,
        ⟨232, false, false, [77365], [5]⟩,
        ⟨2038, false, false, [], [3, 5]⟩,
        ⟨2039, false, false, [], [3, 5]⟩,
        ⟨2036, false, false, [], [3, 5]⟩,
        ⟨2037, false, false, [], [3, 5]⟩,
        ⟨2037, false, false, [], [3, 5]⟩,
        ⟨2049, false, false, [245], [5]⟩,
        ⟨2058, false, false, [], [5]⟩,
        ⟨2059, false, false, [], [5]⟩,
        ⟨2057, false, false, [245], [5]⟩,
        ⟨1606, true, false, [], [77367, 5]⟩,
        ⟨2058, false, false, [], [5]⟩,
        ⟨2059, false, false, [], [5]⟩,
        ⟨2059, false, false, [], [5]⟩,
        ⟨2067, false, false, [245], []⟩,
        ⟨2079, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77369], [245, 77369], .contexts []⟩,
    ⟨[77369, 11], [77369, 11], .contexts []⟩,
    ⟨[77369, 13], [77249], .contexts [
        ⟨2071, true, false, [], [13]⟩,
        ⟨283, false, false, [77367], []⟩,
        ⟨284, false, false, [77367], []⟩,
        ⟨2061, false, false, [], [5]⟩,
        ⟨2062, false, false, [], [5]⟩,
        ⟨1425, false, false, [], [5]⟩,
        ⟨1190, false, false, [], [5]⟩,
        ⟨1190, false, false, [], [5]⟩,
        ⟨1706, false, false, [], []⟩,
        ⟨1423, false, false, [], []⟩,
        ⟨1193, false, false, [], []⟩,
        ⟨1193, false, false, [], []⟩,
        ⟨1710, false, false, [], []⟩,
        ⟨1118, true, false, [], [77249]⟩
      ]⟩,
    ⟨[77249, 13], [77369], .contexts [
        ⟨2083, true, false, [], [13]⟩,
        ⟨98, false, false, [77369], []⟩,
        ⟨2070, false, false, [], []⟩
      ]⟩,
    ⟨[329, 77369], [329, 77369], .contexts []⟩,
    ⟨[77367, 15, 5], [329, 77369], .contexts [
        ⟨2065, false, false, [], [5]⟩,
        ⟨2065, false, false, [], [5]⟩,
        ⟨2052, true, false, [], [15, 5]⟩,
        ⟨245, false, false, [77365], [5]⟩,
        ⟨246, false, false, [77365], [5]⟩,
        ⟨2045, false, false, [], [3, 5]⟩,
        ⟨2047, false, false, [], [3, 5]⟩,
        ⟨2042, false, false, [], [3, 5]⟩,
        ⟨2043, false, false, [], [3, 5]⟩,
        ⟨2043, false, false, [], [3, 5]⟩,
        ⟨2049, false, false, [329], [5]⟩,
        ⟨2063, false, false, [], [5]⟩,
        ⟨2064, false, false, [], [5]⟩,
        ⟨2057, false, false, [329], [5]⟩,
        ⟨2046, true, false, [], [77367, 5]⟩,
        ⟨2063, false, false, [], [5]⟩,
        ⟨2064, false, false, [], [5]⟩,
        ⟨2064, false, false, [], [5]⟩,
        ⟨2067, false, false, [329], []⟩,
        ⟨2085, false, false, [], []⟩
      ]⟩,
    ⟨[329, 77369], [329, 77369], .contexts []⟩,
    ⟨[77369, 15], [77369, 15], .contexts []⟩,
    ⟨[77369, 15], [329, 77369], .contexts [
        ⟨2088, false, false, [], []⟩,
        ⟨2071, true, false, [], [15]⟩,
        ⟨290, false, false, [77367], []⟩,
        ⟨291, false, false, [77367], []⟩,
        ⟨2086, false, false, [], []⟩,
        ⟨2087, false, false, [], []⟩,
        ⟨2078, false, false, [329], []⟩,
        ⟨2046, true, false, [], [77369]⟩
      ]⟩,
    ⟨[77371], [77369, 1], .source 38750⟩,
    ⟨[77369, 1], [77371], .contexts [
        ⟨2090, true, false, [], []⟩
      ]⟩,
    ⟨[77371, 1], [77369], .contexts [
        ⟨2091, true, false, [], [1]⟩,
        ⟨18, false, false, [77369], []⟩,
        ⟨2070, false, false, [], []⟩
      ]⟩,
    ⟨[77371], [77371], .contexts []⟩,
    ⟨[77371], [77371], .contexts []⟩,
    ⟨[77369, 1], [77371], .contexts [
        ⟨2091, false, false, [], []⟩,
        ⟨2093, false, false, [], []⟩,
        ⟨2094, false, false, [], []⟩,
        ⟨2094, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77371], [245, 77371], .contexts []⟩,
    ⟨[245, 77371], [245, 77371], .contexts []⟩,
    ⟨[77371], [77371], .contexts []⟩,
    ⟨[77371, 11], [245, 77371], .contexts [
        ⟨2095, true, false, [], [11]⟩,
        ⟨181, false, false, [77369], []⟩,
        ⟨182, false, false, [77369], []⟩,
        ⟨2082, false, false, [], [1]⟩,
        ⟨2082, false, false, [], [1]⟩,
        ⟨2071, true, false, [], [11, 1]⟩,
        ⟨275, false, false, [77367], [1]⟩,
        ⟨276, false, false, [77367], [1]⟩,
        ⟨2080, false, false, [], [1]⟩,
        ⟨2081, false, false, [], [1]⟩,
        ⟨2078, false, false, [245], [1]⟩,
        ⟨1606, true, false, [], [77369, 1]⟩,
        ⟨2079, false, false, [], [1]⟩,
        ⟨2081, false, false, [], [1]⟩,
        ⟨2081, false, false, [], [1]⟩,
        ⟨2091, false, false, [245], []⟩,
        ⟨2096, false, false, [], []⟩,
        ⟨2097, false, false, [], []⟩,
        ⟨2098, false, false, [245], []⟩
      ]⟩,
    ⟨[329, 77371], [329, 77371], .contexts []⟩,
    ⟨[329, 77371], [329, 77371], .contexts []⟩,
    ⟨[77371, 15], [77371, 15], .contexts []⟩,
    ⟨[77373], [77371, 9], .source 38751⟩,
    ⟨[77371, 9], [77373], .contexts [
        ⟨2103, true, false, [], []⟩
      ]⟩,
    ⟨[77373, 9], [77371], .contexts [
        ⟨2104, true, false, [], [9]⟩,
        ⟨76, false, false, [77371], []⟩,
        ⟨2094, false, false, [], []⟩
      ]⟩,
    ⟨[77373], [77373], .contexts []⟩,
    ⟨[77371, 1], [77369], .contexts [
        ⟨2092, false, false, [], []⟩,
        ⟨2069, false, false, [], []⟩,
        ⟨2070, false, false, [], []⟩,
        ⟨2070, false, false, [], []⟩
      ]⟩,
    ⟨[277, 77371], [277, 77371], .contexts []⟩,
    ⟨[277, 77371], [277, 77371], .contexts []⟩,
    ⟨[277, 77371], [277, 77371], .contexts []⟩,
    ⟨[277, 77373], [277, 77373], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 033. -/
def y322TCContextRaw033 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[277, 77373], [277, 77373], .contexts []⟩,
    ⟨[277, 77373], [277, 77373], .contexts []⟩,
    ⟨[77371, 1, 9, 1, 9], [277, 77373], .contexts [
        ⟨2107, false, false, [], [9, 1, 9]⟩,
        ⟨2071, true, false, [], [9, 1, 9]⟩,
        ⟨2076, false, false, [77367], [1, 9]⟩,
        ⟨2077, false, false, [77367], [1, 9]⟩,
        ⟨2074, false, false, [], [1, 9]⟩,
        ⟨2075, false, false, [], [1, 9]⟩,
        ⟨2078, false, false, [277], [1, 9]⟩,
        ⟨2034, true, false, [], [77369, 1, 9]⟩,
        ⟨2072, false, false, [], [1, 9]⟩,
        ⟨2075, false, false, [], [1, 9]⟩,
        ⟨2075, false, false, [], [1, 9]⟩,
        ⟨2091, false, false, [277], [9]⟩,
        ⟨2108, false, false, [], [9]⟩,
        ⟨2109, false, false, [], [9]⟩,
        ⟨2110, false, false, [], [9]⟩,
        ⟨2104, false, false, [277], []⟩,
        ⟨2111, false, false, [], []⟩,
        ⟨2112, false, false, [], []⟩,
        ⟨2113, false, false, [], []⟩
      ]⟩,
    ⟨[77373, 1], [77373, 1], .contexts []⟩,
    ⟨[77375], [77373, 11], .source 38752⟩,
    ⟨[77373, 11], [77375], .contexts [
        ⟨2116, true, false, [], []⟩
      ]⟩,
    ⟨[77375], [77375], .contexts []⟩,
    ⟨[77375], [77375], .contexts []⟩,
    ⟨[77373, 11], [77375], .contexts [
        ⟨2117, false, false, [], []⟩,
        ⟨2118, false, false, [], []⟩,
        ⟨2119, false, false, [], []⟩,
        ⟨2119, false, false, [], []⟩
      ]⟩,
    ⟨[277, 77375], [277, 77375], .contexts []⟩,
    ⟨[277, 77375], [277, 77375], .contexts []⟩,
    ⟨[77373, 1, 11], [277, 77375], .contexts [
        ⟨2115, false, false, [], [11]⟩,
        ⟨2115, false, false, [], [11]⟩,
        ⟨2106, true, false, [], [1, 11]⟩,
        ⟨2106, true, false, [], [1, 11]⟩,
        ⟨2104, true, false, [], [1, 11]⟩,
        ⟨1143, false, false, [77371], [11]⟩,
        ⟨1146, false, false, [77371], [11]⟩,
        ⟨2114, false, false, [], [11]⟩,
        ⟨2034, true, false, [], [77373, 11]⟩,
        ⟨2111, false, false, [], [11]⟩,
        ⟨2113, false, false, [], [11]⟩,
        ⟨2113, false, false, [], [11]⟩,
        ⟨2117, false, false, [277], []⟩,
        ⟨2121, false, false, [], []⟩,
        ⟨2122, false, false, [], []⟩
      ]⟩,
    ⟨[77375], [77375], .contexts []⟩,
    ⟨[77375, 1], [277, 77375], .contexts [
        ⟨2120, true, false, [], [1]⟩,
        ⟨992, false, false, [77373], []⟩,
        ⟨993, false, false, [77373], []⟩,
        ⟨2123, false, false, [], []⟩,
        ⟨2124, false, false, [277], []⟩,
        ⟨2034, true, false, [], [77375]⟩
      ]⟩,
    ⟨[245, 77375], [245, 77375], .contexts []⟩,
    ⟨[245, 77375], [245, 77375], .contexts []⟩,
    ⟨[77375, 9], [77375, 9], .contexts []⟩,
    ⟨[77375, 9], [245, 77375], .contexts [
        ⟨2128, false, false, [], []⟩,
        ⟨2120, true, false, [], [9]⟩,
        ⟨344, false, false, [77373], []⟩,
        ⟨346, false, false, [77373], []⟩,
        ⟨2105, false, false, [], [11, 9, 11]⟩,
        ⟨2093, false, false, [], [11, 9, 11]⟩,
        ⟨2094, false, false, [], [11, 9, 11]⟩,
        ⟨2094, false, false, [], [11, 9, 11]⟩,
        ⟨2099, false, false, [], [9, 11]⟩,
        ⟨1606, true, false, [], [77371, 9, 11]⟩,
        ⟨2096, false, false, [], [9, 11]⟩,
        ⟨2097, false, false, [], [9, 11]⟩,
        ⟨2097, false, false, [], [9, 11]⟩,
        ⟨2104, false, false, [245], [11]⟩,
        ⟨2117, false, false, [245], []⟩,
        ⟨2126, false, false, [], []⟩,
        ⟨2127, false, false, [], []⟩,
        ⟨2124, false, false, [245], []⟩
      ]⟩,
    ⟨[77377], [77375, 13], .source 38753⟩,
    ⟨[77375, 13], [77377], .contexts [
        ⟨2130, true, false, [], []⟩
      ]⟩,
    ⟨[77377], [77377], .contexts []⟩,
    ⟨[77377], [77377], .contexts []⟩,
    ⟨[77377], [77377], .contexts []⟩,
    ⟨[77379], [77377, 15], .source 38754⟩,
    ⟨[77377, 15], [77379], .contexts [
        ⟨2135, true, false, [], []⟩
      ]⟩,
    ⟨[77379], [77379], .contexts []⟩,
    ⟨[77381], [77379, 1], .source 38755⟩,
    ⟨[77379, 1], [77381], .contexts [
        ⟨2138, true, false, [], []⟩
      ]⟩,
    ⟨[77383], [77381, 3], .source 38756⟩,
    ⟨[77381, 3], [77383], .contexts [
        ⟨2140, true, false, [], []⟩
      ]⟩,
    ⟨[77381], [77381], .contexts []⟩,
    ⟨[77385], [77383, 5], .source 38757⟩,
    ⟨[77383, 5], [77385], .contexts [
        ⟨2143, true, false, [], []⟩
      ]⟩,
    ⟨[77383], [77383], .contexts []⟩,
    ⟨[77385, 5], [77383], .contexts [
        ⟨2144, true, false, [], [5]⟩,
        ⟨49, false, false, [77383], []⟩,
        ⟨2145, false, false, [], []⟩
      ]⟩,
    ⟨[77387], [77385, 1], .source 38758⟩,
    ⟨[77385, 1], [77387], .contexts [
        ⟨2147, true, false, [], []⟩
      ]⟩,
    ⟨[77385], [77385], .contexts []⟩,
    ⟨[77389], [77387, 9], .source 38759⟩,
    ⟨[77387, 9], [77389], .contexts [
        ⟨2150, true, false, [], []⟩
      ]⟩,
    ⟨[77387], [77387], .contexts []⟩,
    ⟨[77389, 9], [77387], .contexts [
        ⟨2151, true, false, [], [9]⟩,
        ⟨76, false, false, [77387], []⟩,
        ⟨2152, false, false, [], []⟩
      ]⟩,
    ⟨[77391], [77389, 11], .source 38760⟩,
    ⟨[77389, 11], [77391], .contexts [
        ⟨2154, true, false, [], []⟩
      ]⟩,
    ⟨[77389], [77389], .contexts []⟩,
    ⟨[77393], [77391, 1], .source 38761⟩,
    ⟨[77391, 1], [77393], .contexts [
        ⟨2157, true, false, [], []⟩
      ]⟩,
    ⟨[77391], [77391], .contexts []⟩,
    ⟨[77395], [77393, 13], .source 38762⟩,
    ⟨[77393, 13], [77395], .contexts [
        ⟨2160, true, false, [], []⟩
      ]⟩,
    ⟨[77393], [77393], .contexts []⟩,
    ⟨[77397], [77395, 15], .source 38763⟩,
    ⟨[77395, 15], [77397], .contexts [
        ⟨2163, true, false, [], []⟩
      ]⟩,
    ⟨[77395], [77395], .contexts []⟩,
    ⟨[77399], [77397, 1], .source 38764⟩,
    ⟨[77397, 1], [77399], .contexts [
        ⟨2166, true, false, [], []⟩
      ]⟩,
    ⟨[77397], [77397], .contexts []⟩,
    ⟨[77401], [77399, 3], .source 38765⟩,
    ⟨[77399, 3], [77401], .contexts [
        ⟨2169, true, false, [], []⟩
      ]⟩,
    ⟨[77399], [77399], .contexts []⟩,
    ⟨[77403], [77401, 5], .source 38766⟩,
    ⟨[77401, 5], [77403], .contexts [
        ⟨2172, true, false, [], []⟩
      ]⟩,
    ⟨[77401], [77401], .contexts []⟩,
    ⟨[77405], [77403, 1], .source 38767⟩]

/-- Exact literal claimed equations and contextual derivations, block 034. -/
def y322TCContextRaw034 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77403, 1], [77405], .contexts [
        ⟨2175, true, false, [], []⟩
      ]⟩,
    ⟨[77403], [77403], .contexts []⟩,
    ⟨[77407], [77405, 9], .source 38768⟩,
    ⟨[77405, 9], [77407], .contexts [
        ⟨2178, true, false, [], []⟩
      ]⟩,
    ⟨[77405], [77405], .contexts []⟩,
    ⟨[77409], [77407, 11], .source 38769⟩,
    ⟨[77407, 11], [77409], .contexts [
        ⟨2181, true, false, [], []⟩
      ]⟩,
    ⟨[77407], [77407], .contexts []⟩,
    ⟨[77411], [77409, 1], .source 38770⟩,
    ⟨[77409, 1], [77411], .contexts [
        ⟨2184, true, false, [], []⟩
      ]⟩,
    ⟨[77409], [77409], .contexts []⟩,
    ⟨[77413], [77411, 13], .source 38771⟩,
    ⟨[77411, 13], [77413], .contexts [
        ⟨2187, true, false, [], []⟩
      ]⟩,
    ⟨[77411], [77411], .contexts []⟩,
    ⟨[77415], [77413, 15], .source 38772⟩,
    ⟨[77413, 15], [77415], .contexts [
        ⟨2190, true, false, [], []⟩
      ]⟩,
    ⟨[77413], [77413], .contexts []⟩,
    ⟨[77417], [77415, 1], .source 38773⟩,
    ⟨[77415, 1], [77417], .contexts [
        ⟨2193, true, false, [], []⟩
      ]⟩,
    ⟨[77415], [77415], .contexts []⟩,
    ⟨[77419], [77417, 3], .source 38774⟩,
    ⟨[77417, 3], [77419], .contexts [
        ⟨2196, true, false, [], []⟩
      ]⟩,
    ⟨[77417], [77417], .contexts []⟩,
    ⟨[77421], [77419, 5], .source 38775⟩,
    ⟨[77419, 5], [77421], .contexts [
        ⟨2199, true, false, [], []⟩
      ]⟩,
    ⟨[77419], [77419], .contexts []⟩,
    ⟨[77423], [77421, 1], .source 38776⟩,
    ⟨[77421, 1], [77423], .contexts [
        ⟨2202, true, false, [], []⟩
      ]⟩,
    ⟨[77421], [77421], .contexts []⟩,
    ⟨[77425], [77423, 9], .source 38777⟩,
    ⟨[77423, 9], [77425], .contexts [
        ⟨2205, true, false, [], []⟩
      ]⟩,
    ⟨[77423], [77423], .contexts []⟩,
    ⟨[77427], [77425, 11], .source 38778⟩,
    ⟨[77425, 11], [77427], .contexts [
        ⟨2208, true, false, [], []⟩
      ]⟩,
    ⟨[77425], [77425], .contexts []⟩,
    ⟨[77429], [77427, 1], .source 38779⟩,
    ⟨[77427], [77427], .contexts []⟩,
    ⟨[77429, 1], [77427], .contexts [
        ⟨2211, false, false, [], [1]⟩,
        ⟨18, false, false, [77427], []⟩,
        ⟨2212, false, false, [], []⟩
      ]⟩,
    ⟨[77431], [77429, 13], .source 38780⟩,
    ⟨[77429], [77429], .contexts []⟩,
    ⟨[77431, 13], [77429], .contexts [
        ⟨2214, false, false, [], [13]⟩,
        ⟨98, false, false, [77429], []⟩,
        ⟨2215, false, false, [], []⟩
      ]⟩,
    ⟨[77433], [77431, 15], .source 38781⟩,
    ⟨[77431], [77431], .contexts []⟩,
    ⟨[77433, 15], [77431], .contexts [
        ⟨2217, false, false, [], [15]⟩,
        ⟨3, false, false, [77431], []⟩,
        ⟨2218, false, false, [], []⟩
      ]⟩,
    ⟨[77435], [77433, 1], .source 38782⟩,
    ⟨[77433], [77433], .contexts []⟩,
    ⟨[77435, 1], [77433], .contexts [
        ⟨2220, false, false, [], [1]⟩,
        ⟨18, false, false, [77433], []⟩,
        ⟨2221, false, false, [], []⟩
      ]⟩,
    ⟨[77437], [77435, 3], .source 38783⟩,
    ⟨[77435], [77435], .contexts []⟩,
    ⟨[77437, 3], [77435], .contexts [
        ⟨2223, false, false, [], [3]⟩,
        ⟨35, false, false, [77435], []⟩,
        ⟨2224, false, false, [], []⟩
      ]⟩,
    ⟨[77439], [77437, 5], .source 38784⟩,
    ⟨[77437], [77437], .contexts []⟩,
    ⟨[77439, 5], [77437], .contexts [
        ⟨2226, false, false, [], [5]⟩,
        ⟨49, false, false, [77437], []⟩,
        ⟨2227, false, false, [], []⟩
      ]⟩,
    ⟨[77441], [77439, 1], .source 38785⟩,
    ⟨[77439, 1], [77441], .contexts [
        ⟨2229, true, false, [], []⟩
      ]⟩,
    ⟨[77439], [77439], .contexts []⟩,
    ⟨[77441, 1], [77439], .contexts [
        ⟨2230, true, false, [], [1]⟩,
        ⟨18, false, false, [77439], []⟩,
        ⟨2231, false, false, [], []⟩
      ]⟩,
    ⟨[77443], [77441, 9], .source 38786⟩,
    ⟨[77441, 9], [77443], .contexts [
        ⟨2233, true, false, [], []⟩
      ]⟩,
    ⟨[77441], [77441], .contexts []⟩,
    ⟨[77443, 9], [77441], .contexts [
        ⟨2234, true, false, [], [9]⟩,
        ⟨76, false, false, [77441], []⟩,
        ⟨2235, false, false, [], []⟩
      ]⟩,
    ⟨[77445], [77443, 11], .source 38787⟩,
    ⟨[77443, 11], [77445], .contexts [
        ⟨2237, true, false, [], []⟩
      ]⟩,
    ⟨[77443], [77443], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 035. -/
def y322TCContextRaw035 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77445, 11], [77443], .contexts [
        ⟨2238, true, false, [], [11]⟩,
        ⟨90, false, false, [77443], []⟩,
        ⟨2239, false, false, [], []⟩
      ]⟩,
    ⟨[77447], [77445, 1], .source 38788⟩,
    ⟨[77445, 1], [77447], .contexts [
        ⟨2241, true, false, [], []⟩
      ]⟩,
    ⟨[77445], [77445], .contexts []⟩,
    ⟨[77447, 1], [77445], .contexts [
        ⟨2242, true, false, [], [1]⟩,
        ⟨18, false, false, [77445], []⟩,
        ⟨2243, false, false, [], []⟩
      ]⟩,
    ⟨[77449], [77447, 13], .source 38789⟩,
    ⟨[77447, 13], [77449], .contexts [
        ⟨2245, true, false, [], []⟩
      ]⟩,
    ⟨[77447], [77447], .contexts []⟩,
    ⟨[77449, 13], [77447], .contexts [
        ⟨2246, true, false, [], [13]⟩,
        ⟨98, false, false, [77447], []⟩,
        ⟨2247, false, false, [], []⟩
      ]⟩,
    ⟨[77451], [77449, 15], .source 38790⟩,
    ⟨[77449, 15], [77451], .contexts [
        ⟨2249, true, false, [], []⟩
      ]⟩,
    ⟨[77449], [77449], .contexts []⟩,
    ⟨[77451, 15], [77449], .contexts [
        ⟨2250, true, false, [], [15]⟩,
        ⟨3, false, false, [77449], []⟩,
        ⟨2251, false, false, [], []⟩
      ]⟩,
    ⟨[77453], [77451, 1], .source 38791⟩,
    ⟨[77451, 1], [77453], .contexts [
        ⟨2253, true, false, [], []⟩
      ]⟩,
    ⟨[77451], [77451], .contexts []⟩,
    ⟨[77453, 1], [77451], .contexts [
        ⟨2254, true, false, [], [1]⟩,
        ⟨18, false, false, [77451], []⟩,
        ⟨2255, false, false, [], []⟩
      ]⟩,
    ⟨[77455], [77453, 3], .source 38792⟩,
    ⟨[77453, 3], [77455], .contexts [
        ⟨2257, true, false, [], []⟩
      ]⟩,
    ⟨[77453], [77453], .contexts []⟩,
    ⟨[77455, 3], [77453], .contexts [
        ⟨2258, true, false, [], [3]⟩,
        ⟨35, false, false, [77453], []⟩,
        ⟨2259, false, false, [], []⟩
      ]⟩,
    ⟨[77457], [77455, 5], .source 38793⟩,
    ⟨[77455], [77455], .contexts []⟩,
    ⟨[77457, 5], [77455], .contexts [
        ⟨2261, false, false, [], [5]⟩,
        ⟨49, false, false, [77455], []⟩,
        ⟨2262, false, false, [], []⟩
      ]⟩,
    ⟨[77459], [77457, 1], .source 38794⟩,
    ⟨[77457], [77457], .contexts []⟩,
    ⟨[77459, 1], [77457], .contexts [
        ⟨2264, false, false, [], [1]⟩,
        ⟨18, false, false, [77457], []⟩,
        ⟨2265, false, false, [], []⟩
      ]⟩,
    ⟨[77461], [77459, 9], .source 38795⟩,
    ⟨[77459], [77459], .contexts []⟩,
    ⟨[77461, 9], [77459], .contexts [
        ⟨2267, false, false, [], [9]⟩,
        ⟨76, false, false, [77459], []⟩,
        ⟨2268, false, false, [], []⟩
      ]⟩,
    ⟨[77463], [77461, 11], .source 38796⟩,
    ⟨[77461], [77461], .contexts []⟩,
    ⟨[77463, 11], [77461], .contexts [
        ⟨2270, false, false, [], [11]⟩,
        ⟨90, false, false, [77461], []⟩,
        ⟨2271, false, false, [], []⟩
      ]⟩,
    ⟨[77465], [77463, 1], .source 38797⟩,
    ⟨[77463], [77463], .contexts []⟩,
    ⟨[77465, 1], [77463], .contexts [
        ⟨2273, false, false, [], [1]⟩,
        ⟨18, false, false, [77463], []⟩,
        ⟨2274, false, false, [], []⟩
      ]⟩,
    ⟨[77467], [77465, 13], .source 38798⟩,
    ⟨[77465, 13], [77467], .contexts [
        ⟨2276, true, false, [], []⟩
      ]⟩,
    ⟨[77465], [77465], .contexts []⟩,
    ⟨[77467, 13], [77465], .contexts [
        ⟨2277, true, false, [], [13]⟩,
        ⟨98, false, false, [77465], []⟩,
        ⟨2278, false, false, [], []⟩
      ]⟩,
    ⟨[77469], [77467, 15], .source 38799⟩,
    ⟨[77467, 15], [77469], .contexts [
        ⟨2280, true, false, [], []⟩
      ]⟩,
    ⟨[77467], [77467], .contexts []⟩,
    ⟨[77469, 15], [77467], .contexts [
        ⟨2281, true, false, [], [15]⟩,
        ⟨3, false, false, [77467], []⟩,
        ⟨2282, false, false, [], []⟩
      ]⟩,
    ⟨[77471], [77469, 1], .source 38800⟩,
    ⟨[77469], [77469], .contexts []⟩,
    ⟨[77471, 1], [77469], .contexts [
        ⟨2284, false, false, [], [1]⟩,
        ⟨18, false, false, [77469], []⟩,
        ⟨2285, false, false, [], []⟩
      ]⟩,
    ⟨[77473], [77471, 3], .source 38801⟩,
    ⟨[77471, 3], [77473], .contexts [
        ⟨2287, true, false, [], []⟩
      ]⟩,
    ⟨[77471], [77471], .contexts []⟩,
    ⟨[77473, 3], [77471], .contexts [
        ⟨2288, true, false, [], [3]⟩,
        ⟨35, false, false, [77471], []⟩,
        ⟨2289, false, false, [], []⟩
      ]⟩,
    ⟨[77475], [77473, 5], .source 38802⟩,
    ⟨[77473], [77473], .contexts []⟩,
    ⟨[77475, 5], [77473], .contexts [
        ⟨2291, false, false, [], [5]⟩,
        ⟨49, false, false, [77473], []⟩,
        ⟨2292, false, false, [], []⟩
      ]⟩,
    ⟨[77477], [77475, 1], .source 38803⟩,
    ⟨[77475, 1], [77477], .contexts [
        ⟨2294, true, false, [], []⟩
      ]⟩,
    ⟨[77475], [77475], .contexts []⟩,
    ⟨[77477], [77477], .contexts []⟩,
    ⟨[77475, 5], [77473], .contexts [
        ⟨2293, false, false, [], []⟩
      ]⟩,
    ⟨[77475, 5], [77473], .contexts [
        ⟨2298, false, false, [], []⟩,
        ⟨2292, false, false, [], []⟩,
        ⟨2292, false, false, [], []⟩
      ]⟩,
    ⟨[77471], [77471], .contexts []⟩,
    ⟨[77471, 1], [77469], .contexts [
        ⟨2286, false, false, [], []⟩
      ]⟩,
    ⟨[77469], [77469], .contexts []⟩,
    ⟨[77469, 15], [77467], .contexts [
        ⟨2283, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 036. -/
def y322TCContextRaw036 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77467], [77467], .contexts []⟩,
    ⟨[77467, 13], [77465], .contexts [
        ⟨2279, false, false, [], []⟩
      ]⟩,
    ⟨[77465], [77465], .contexts []⟩,
    ⟨[77465, 1], [77463], .contexts [
        ⟨2275, false, false, [], []⟩
      ]⟩,
    ⟨[77463], [77463], .contexts []⟩,
    ⟨[77475, 5, 3, 1, 15, 13, 1], [77463], .contexts [
        ⟨2299, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨2290, false, false, [], [1, 15, 13, 1]⟩,
        ⟨2300, false, false, [], [1, 15, 13, 1]⟩,
        ⟨2289, false, false, [], [1, 15, 13, 1]⟩,
        ⟨2289, false, false, [], [1, 15, 13, 1]⟩,
        ⟨2301, false, false, [], [15, 13, 1]⟩,
        ⟨2302, false, false, [], [15, 13, 1]⟩,
        ⟨2285, false, false, [], [15, 13, 1]⟩,
        ⟨2285, false, false, [], [15, 13, 1]⟩,
        ⟨2303, false, false, [], [13, 1]⟩,
        ⟨2304, false, false, [], [13, 1]⟩,
        ⟨2282, false, false, [], [13, 1]⟩,
        ⟨2282, false, false, [], [13, 1]⟩,
        ⟨2305, false, false, [], [1]⟩,
        ⟨2306, false, false, [], [1]⟩,
        ⟨2278, false, false, [], [1]⟩,
        ⟨2278, false, false, [], [1]⟩,
        ⟨2307, false, false, [], []⟩,
        ⟨2308, false, false, [], []⟩,
        ⟨2274, false, false, [], []⟩,
        ⟨2274, false, false, [], []⟩
      ]⟩,
    ⟨[77461, 9], [77459], .contexts [
        ⟨2269, false, false, [], []⟩
      ]⟩,
    ⟨[77459], [77459], .contexts []⟩,
    ⟨[77459, 1], [77457], .contexts [
        ⟨2266, false, false, [], []⟩
      ]⟩,
    ⟨[77457], [77457], .contexts []⟩,
    ⟨[77455, 3], [77453], .contexts [
        ⟨2260, false, false, [], []⟩
      ]⟩,
    ⟨[77453], [77453], .contexts []⟩,
    ⟨[77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3], [77453], .contexts [
        ⟨2309, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨2272, false, false, [], [9, 1, 5, 3]⟩,
        ⟨2271, false, false, [], [9, 1, 5, 3]⟩,
        ⟨2271, false, false, [], [9, 1, 5, 3]⟩,
        ⟨2310, false, false, [], [1, 5, 3]⟩,
        ⟨2311, false, false, [], [1, 5, 3]⟩,
        ⟨2268, false, false, [], [1, 5, 3]⟩,
        ⟨2268, false, false, [], [1, 5, 3]⟩,
        ⟨2312, false, false, [], [5, 3]⟩,
        ⟨2313, false, false, [], [5, 3]⟩,
        ⟨2265, false, false, [], [5, 3]⟩,
        ⟨2265, false, false, [], [5, 3]⟩,
        ⟨2263, false, false, [], [3]⟩,
        ⟨2262, false, false, [], [3]⟩,
        ⟨2262, false, false, [], [3]⟩,
        ⟨2314, false, false, [], []⟩,
        ⟨2315, false, false, [], []⟩,
        ⟨2259, false, false, [], []⟩,
        ⟨2259, false, false, [], []⟩
      ]⟩,
    ⟨[77453, 1], [77451], .contexts [
        ⟨2256, false, false, [], []⟩
      ]⟩,
    ⟨[77451], [77451], .contexts []⟩,
    ⟨[77451, 15], [77449], .contexts [
        ⟨2252, false, false, [], []⟩
      ]⟩,
    ⟨[77449], [77449], .contexts []⟩,
    ⟨[77449, 13], [77447], .contexts [
        ⟨2248, false, false, [], []⟩
      ]⟩,
    ⟨[77447], [77447], .contexts []⟩,
    ⟨[77447, 1], [77445], .contexts [
        ⟨2244, false, false, [], []⟩
      ]⟩,
    ⟨[77445], [77445], .contexts []⟩,
    ⟨[77445, 11], [77443], .contexts [
        ⟨2240, false, false, [], []⟩
      ]⟩,
    ⟨[77443], [77443], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [77443], .contexts [
        ⟨2316, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨2317, false, false, [], [15, 13, 1, 11]⟩,
        ⟨2318, false, false, [], [15, 13, 1, 11]⟩,
        ⟨2255, false, false, [], [15, 13, 1, 11]⟩,
        ⟨2255, false, false, [], [15, 13, 1, 11]⟩,
        ⟨2319, false, false, [], [13, 1, 11]⟩,
        ⟨2320, false, false, [], [13, 1, 11]⟩,
        ⟨2251, false, false, [], [13, 1, 11]⟩,
        ⟨2251, false, false, [], [13, 1, 11]⟩,
        ⟨2321, false, false, [], [1, 11]⟩,
        ⟨2322, false, false, [], [1, 11]⟩,
        ⟨2247, false, false, [], [1, 11]⟩,
        ⟨2247, false, false, [], [1, 11]⟩,
        ⟨2323, false, false, [], [11]⟩,
        ⟨2324, false, false, [], [11]⟩,
        ⟨2243, false, false, [], [11]⟩,
        ⟨2243, false, false, [], [11]⟩,
        ⟨2325, false, false, [], []⟩,
        ⟨2326, false, false, [], []⟩,
        ⟨2239, false, false, [], []⟩,
        ⟨2239, false, false, [], []⟩
      ]⟩,
    ⟨[77443, 9], [77441], .contexts [
        ⟨2236, false, false, [], []⟩
      ]⟩,
    ⟨[77441], [77441], .contexts []⟩,
    ⟨[77441, 1], [77439], .contexts [
        ⟨2232, false, false, [], []⟩
      ]⟩,
    ⟨[77439], [77439], .contexts []⟩,
    ⟨[77439, 5], [77437], .contexts [
        ⟨2228, false, false, [], []⟩
      ]⟩,
    ⟨[77437], [77437], .contexts []⟩,
    ⟨[77437, 3], [77435], .contexts [
        ⟨2225, false, false, [], []⟩
      ]⟩,
    ⟨[77435], [77435], .contexts []⟩,
    ⟨[77435, 1], [77433], .contexts [
        ⟨2222, false, false, [], []⟩
      ]⟩,
    ⟨[77433], [77433], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [77433], .contexts [
        ⟨2327, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨2328, false, false, [], [1, 5, 3, 1]⟩,
        ⟨2329, false, false, [], [1, 5, 3, 1]⟩,
        ⟨2235, false, false, [], [1, 5, 3, 1]⟩,
        ⟨2235, false, false, [], [1, 5, 3, 1]⟩,
        ⟨2330, false, false, [], [5, 3, 1]⟩,
        ⟨2331, false, false, [], [5, 3, 1]⟩,
        ⟨2231, false, false, [], [5, 3, 1]⟩,
        ⟨2231, false, false, [], [5, 3, 1]⟩,
        ⟨2332, false, false, [], [3, 1]⟩,
        ⟨2333, false, false, [], [3, 1]⟩,
        ⟨2227, false, false, [], [3, 1]⟩,
        ⟨2227, false, false, [], [3, 1]⟩,
        ⟨2334, false, false, [], [1]⟩,
        ⟨2335, false, false, [], [1]⟩,
        ⟨2224, false, false, [], [1]⟩,
        ⟨2224, false, false, [], [1]⟩,
        ⟨2336, false, false, [], []⟩,
        ⟨2337, false, false, [], []⟩,
        ⟨2221, false, false, [], []⟩,
        ⟨2221, false, false, [], []⟩
      ]⟩,
    ⟨[77431, 13], [77429], .contexts [
        ⟨2216, false, false, [], []⟩
      ]⟩,
    ⟨[77429], [77429], .contexts []⟩,
    ⟨[77427], [77427], .contexts []⟩,
    ⟨[77425], [77425], .contexts []⟩,
    ⟨[77423], [77423], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9
    ], [77423], .contexts [
        ⟨2338, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨2219, false, false, [], [13, 1, 11, 9]⟩,
        ⟨2218, false, false, [], [13, 1, 11, 9]⟩,
        ⟨2218, false, false, [], [13, 1, 11, 9]⟩,
        ⟨2339, false, false, [], [1, 11, 9]⟩,
        ⟨2340, false, false, [], [1, 11, 9]⟩,
        ⟨2215, false, false, [], [1, 11, 9]⟩,
        ⟨2215, false, false, [], [1, 11, 9]⟩,
        ⟨2213, false, false, [], [11, 9]⟩,
        ⟨2341, false, false, [], [11, 9]⟩,
        ⟨2212, false, false, [], [11, 9]⟩,
        ⟨2212, false, false, [], [11, 9]⟩,
        ⟨2209, true, false, [], [11, 9]⟩,
        ⟨90, false, false, [77425], [9]⟩,
        ⟨2210, false, false, [], [9]⟩,
        ⟨2342, false, false, [], [9]⟩,
        ⟨2210, false, false, [], [9]⟩,
        ⟨2210, false, false, [], [9]⟩,
        ⟨2206, true, false, [], [9]⟩,
        ⟨76, false, false, [77423], []⟩,
        ⟨2207, false, false, [], []⟩,
        ⟨2343, false, false, [], []⟩,
        ⟨2207, false, false, [], []⟩,
        ⟨2207, false, false, [], []⟩
      ]⟩,
    ⟨[77421], [77421], .contexts []⟩,
    ⟨[77419], [77419], .contexts []⟩,
    ⟨[77417], [77417], .contexts []⟩,
    ⟨[77415], [77415], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1
    ], [77415], .contexts [
        ⟨2344, false, false, [], [1, 5, 3, 1]⟩,
        ⟨2203, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [77421], [5, 3, 1]⟩,
        ⟨2204, false, false, [], [5, 3, 1]⟩,
        ⟨2345, false, false, [], [5, 3, 1]⟩,
        ⟨2204, false, false, [], [5, 3, 1]⟩,
        ⟨2204, false, false, [], [5, 3, 1]⟩,
        ⟨2200, true, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [77419], [3, 1]⟩,
        ⟨2201, false, false, [], [3, 1]⟩,
        ⟨2346, false, false, [], [3, 1]⟩,
        ⟨2201, false, false, [], [3, 1]⟩,
        ⟨2201, false, false, [], [3, 1]⟩,
        ⟨2197, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [77417], [1]⟩,
        ⟨2198, false, false, [], [1]⟩,
        ⟨2347, false, false, [], [1]⟩,
        ⟨2198, false, false, [], [1]⟩,
        ⟨2198, false, false, [], [1]⟩,
        ⟨2194, true, false, [], [1]⟩,
        ⟨18, false, false, [77415], []⟩,
        ⟨2195, false, false, [], []⟩,
        ⟨2348, false, false, [], []⟩,
        ⟨2195, false, false, [], []⟩,
        ⟨2195, false, false, [], []⟩
      ]⟩,
    ⟨[77413], [77413], .contexts []⟩,
    ⟨[77411], [77411], .contexts []⟩,
    ⟨[77409], [77409], .contexts []⟩,
    ⟨[77407], [77407], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [77407], .contexts [
        ⟨2349, false, false, [], [15, 13, 1, 11]⟩,
        ⟨2191, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77413], [13, 1, 11]⟩,
        ⟨2192, false, false, [], [13, 1, 11]⟩,
        ⟨2350, false, false, [], [13, 1, 11]⟩,
        ⟨2192, false, false, [], [13, 1, 11]⟩,
        ⟨2192, false, false, [], [13, 1, 11]⟩,
        ⟨2188, true, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [77411], [1, 11]⟩,
        ⟨2189, false, false, [], [1, 11]⟩,
        ⟨2351, false, false, [], [1, 11]⟩,
        ⟨2189, false, false, [], [1, 11]⟩,
        ⟨2189, false, false, [], [1, 11]⟩,
        ⟨2185, true, false, [], [1, 11]⟩,
        ⟨18, false, false, [77409], [11]⟩,
        ⟨2186, false, false, [], [11]⟩,
        ⟨2352, false, false, [], [11]⟩,
        ⟨2186, false, false, [], [11]⟩,
        ⟨2186, false, false, [], [11]⟩,
        ⟨2182, true, false, [], [11]⟩,
        ⟨90, false, false, [77407], []⟩,
        ⟨2183, false, false, [], []⟩,
        ⟨2353, false, false, [], []⟩,
        ⟨2183, false, false, [], []⟩,
        ⟨2183, false, false, [], []⟩
      ]⟩,
    ⟨[77405], [77405], .contexts []⟩,
    ⟨[77403], [77403], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [77399], .contexts [
        ⟨2354, false, false, [], [9, 1, 5, 3]⟩,
        ⟨2179, true, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [77405], [1, 5, 3]⟩,
        ⟨2180, false, false, [], [1, 5, 3]⟩,
        ⟨2355, false, false, [], [1, 5, 3]⟩,
        ⟨2180, false, false, [], [1, 5, 3]⟩,
        ⟨2180, false, false, [], [1, 5, 3]⟩,
        ⟨2176, true, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [77403], [5, 3]⟩,
        ⟨2177, false, false, [], [5, 3]⟩,
        ⟨2356, false, false, [], [5, 3]⟩,
        ⟨2177, false, false, [], [5, 3]⟩,
        ⟨2177, false, false, [], [5, 3]⟩,
        ⟨2173, true, false, [], [5, 3]⟩,
        ⟨49, false, false, [77401], [3]⟩,
        ⟨2174, false, false, [], [3]⟩,
        ⟨2174, false, false, [], [3]⟩,
        ⟨2174, false, false, [], [3]⟩,
        ⟨2170, true, false, [], [3]⟩,
        ⟨35, false, false, [77399], []⟩,
        ⟨2171, false, false, [], []⟩,
        ⟨2171, false, false, [], []⟩,
        ⟨2171, false, false, [], []⟩
      ]⟩,
    ⟨[77397], [77397], .contexts []⟩,
    ⟨[77393], [77393], .contexts []⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [77391], .contexts [
        ⟨2357, false, false, [], [1, 15, 13, 1]⟩,
        ⟨2167, true, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [77397], [15, 13, 1]⟩,
        ⟨2168, false, false, [], [15, 13, 1]⟩,
        ⟨2358, false, false, [], [15, 13, 1]⟩,
        ⟨2168, false, false, [], [15, 13, 1]⟩,
        ⟨2168, false, false, [], [15, 13, 1]⟩,
        ⟨2164, true, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [77395], [13, 1]⟩,
        ⟨2165, false, false, [], [13, 1]⟩,
        ⟨2165, false, false, [], [13, 1]⟩,
        ⟨2165, false, false, [], [13, 1]⟩,
        ⟨2161, true, false, [], [13, 1]⟩,
        ⟨98, false, false, [77393], [1]⟩,
        ⟨2162, false, false, [], [1]⟩,
        ⟨2359, false, false, [], [1]⟩,
        ⟨2162, false, false, [], [1]⟩,
        ⟨2162, false, false, [], [1]⟩,
        ⟨2158, true, false, [], [1]⟩,
        ⟨18, false, false, [77391], []⟩,
        ⟨2159, false, false, [], []⟩,
        ⟨2159, false, false, [], []⟩,
        ⟨2159, false, false, [], []⟩
      ]⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [77383], .contexts [
        ⟨2360, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2155, true, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [77389], [9, 1, 5]⟩,
        ⟨2156, false, false, [], [9, 1, 5]⟩,
        ⟨2156, false, false, [], [9, 1, 5]⟩,
        ⟨2156, false, false, [], [9, 1, 5]⟩,
        ⟨2153, false, false, [], [1, 5]⟩,
        ⟨2152, false, false, [], [1, 5]⟩,
        ⟨2152, false, false, [], [1, 5]⟩,
        ⟨2148, true, false, [], [1, 5]⟩,
        ⟨18, false, false, [77385], [5]⟩,
        ⟨2149, false, false, [], [5]⟩,
        ⟨2149, false, false, [], [5]⟩,
        ⟨2149, false, false, [], [5]⟩,
        ⟨2146, false, false, [], []⟩,
        ⟨2145, false, false, [], []⟩,
        ⟨2145, false, false, [], []⟩
      ]⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [77375], .contexts [
        ⟨2361, false, false, [], [3, 1, 15, 13]⟩,
        ⟨2141, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [77381], [1, 15, 13]⟩,
        ⟨2142, false, false, [], [1, 15, 13]⟩,
        ⟨2142, false, false, [], [1, 15, 13]⟩,
        ⟨2142, false, false, [], [1, 15, 13]⟩,
        ⟨2139, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [77379], [15, 13]⟩,
        ⟨2137, false, false, [], [15, 13]⟩,
        ⟨2137, false, false, [], [15, 13]⟩,
        ⟨2137, false, false, [], [15, 13]⟩,
        ⟨2136, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [77377], [13]⟩,
        ⟨2133, false, false, [], [13]⟩,
        ⟨2132, false, false, [], [13]⟩,
        ⟨2133, false, false, [], [13]⟩,
        ⟨2133, false, false, [], [13]⟩,
        ⟨2131, true, false, [], [13]⟩,
        ⟨98, false, false, [77375], []⟩,
        ⟨2119, false, false, [], []⟩,
        ⟨2118, false, false, [], []⟩,
        ⟨2119, false, false, [], []⟩,
        ⟨2119, false, false, [], []⟩
      ]⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [277, 77367], .contexts [
        ⟨2362, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨2125, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2121, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2122, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2122, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2117, true, false, [277], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [277, 77373], [9, 1, 5]⟩,
        ⟨2106, false, false, [277], [9, 1, 5]⟩,
        ⟨2111, false, false, [], [9, 1, 5]⟩,
        ⟨2112, false, false, [], [9, 1, 5]⟩,
        ⟨2113, false, false, [], [9, 1, 5]⟩,
        ⟨2105, false, false, [277], [1, 5]⟩,
        ⟨2108, false, false, [], [1, 5]⟩,
        ⟨2109, false, false, [], [1, 5]⟩,
        ⟨2110, false, false, [], [1, 5]⟩,
        ⟨2092, false, false, [277], [5]⟩,
        ⟨2072, false, false, [], [5]⟩,
        ⟨2073, false, false, [], [5]⟩,
        ⟨2075, false, false, [], [5]⟩,
        ⟨2068, false, false, [277], []⟩,
        ⟨2053, false, false, [], []⟩,
        ⟨2054, false, false, [], []⟩,
        ⟨2055, false, false, [], []⟩
      ]⟩,
    ⟨[331], [277, 31], .source 230⟩,
    ⟨[333], [331, 329], .source 231⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [333, 77245], .contexts [
        ⟨2363, false, false, [], [3, 1, 15, 13]⟩,
        ⟨2049, true, false, [277], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [277, 77365], [1, 15, 13]⟩,
        ⟨2025, false, false, [277], [1, 15, 13]⟩,
        ⟨2030, false, false, [], [1, 15, 13]⟩,
        ⟨2031, false, false, [], [1, 15, 13]⟩,
        ⟨2032, false, false, [], [1, 15, 13]⟩,
        ⟨2029, false, false, [277], [15, 13]⟩,
        ⟨740, true, false, [277], [77365, 15, 13]⟩,
        ⟨2364, true, false, [], [77365, 15, 13]⟩,
        ⟨2047, false, false, [331], [13]⟩,
        ⟨2365, true, false, [], [77365, 13]⟩,
        ⟨2024, false, false, [333], []⟩
      ]⟩,
    ⟨[335], [333, 243], .source 232⟩]

/-- Exact literal claimed equations and contextual derivations, block 037. -/
def y322TCContextRaw037 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[337], [335, 243], .source 233⟩,
    ⟨[339], [337, 19], .source 234⟩,
    ⟨[341], [339, 291], .source 235⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [341, 77363], .contexts [
        ⟨2366, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨1184, false, false, [333], [11, 9, 1, 5]⟩,
        ⟨1643, false, false, [333], [9, 1, 5]⟩,
        ⟨2367, true, false, [], [77243, 9, 1, 5]⟩,
        ⟨1640, false, false, [335], [1, 5]⟩,
        ⟨2368, true, false, [], [77117, 1, 5]⟩,
        ⟨403, false, false, [337], [5]⟩,
        ⟨735, true, false, [337], [77117, 5]⟩,
        ⟨2369, true, false, [], [77117, 5]⟩,
        ⟨1929, true, false, [339, 288], [5]⟩,
        ⟨49, false, false, [339, 288, 77363], []⟩,
        ⟨1848, true, false, [339], [77363]⟩,
        ⟨2370, true, false, [], [77363]⟩
      ]⟩,
    ⟨[343], [341, 153], .source 236⟩,
    ⟨[345], [343, 135], .source 237⟩,
    ⟨[347], [345, 287], .source 238⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [347, 77235], .contexts [
        ⟨2371, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨1925, false, false, [341], [1, 15, 13, 1]⟩,
        ⟨2372, true, false, [], [77363, 1, 15, 13, 1]⟩,
        ⟨1921, false, false, [343], [15, 13, 1]⟩,
        ⟨2373, true, false, [], [77363, 15, 13, 1]⟩,
        ⟨1913, true, false, [345], [15, 13, 1]⟩,
        ⟨3, false, false, [345, 77215], [13, 1]⟩,
        ⟨596, false, false, [345], [13, 1]⟩,
        ⟨1840, false, false, [345], [1]⟩,
        ⟨2374, true, false, [], [77361, 1]⟩,
        ⟨1821, false, false, [347], []⟩
      ]⟩,
    ⟨[349], [347, 111], .source 239⟩,
    ⟨[351], [349, 21], .source 240⟩,
    ⟨[353], [351, 23], .source 241⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [353, 77107], .contexts [
        ⟨2375, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨1119, false, false, [347], [9, 1, 5, 3]⟩,
        ⟨845, false, false, [347], [1, 5, 3]⟩,
        ⟨2376, true, false, [], [77105, 1, 5, 3]⟩,
        ⟨220, false, false, [349], [5, 3]⟩,
        ⟨736, true, false, [349], [77105, 5, 3]⟩,
        ⟨2377, true, false, [], [77105, 5, 3]⟩,
        ⟨250, false, false, [351], [3]⟩,
        ⟨270, false, false, [351], []⟩,
        ⟨749, true, false, [351], [77107]⟩,
        ⟨2378, true, false, [], [77107]⟩
      ]⟩,
    ⟨[355], [353, 21], .source 242⟩,
    ⟨[357], [355, 31], .source 243⟩,
    ⟨[359], [357, 19], .source 244⟩,
    ⟨[361], [359, 21], .source 245⟩,
    ⟨[363], [361, 29], .source 246⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [363, 77107], .contexts [
        ⟨2379, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨259, false, false, [353], [15, 13, 1, 11]⟩,
        ⟨736, true, false, [353], [77107, 15, 13, 1, 11]⟩,
        ⟨2380, true, false, [], [77107, 15, 13, 1, 11]⟩,
        ⟨293, false, false, [355], [13, 1, 11]⟩,
        ⟨740, true, false, [355], [77107, 13, 1, 11]⟩,
        ⟨2381, true, false, [], [77107, 13, 1, 11]⟩,
        ⟨286, false, false, [357], [1, 11]⟩,
        ⟨735, true, false, [357], [77107, 1, 11]⟩,
        ⟨2382, true, false, [], [77107, 1, 11]⟩,
        ⟨259, false, false, [359], [11]⟩,
        ⟨736, true, false, [359], [77107, 11]⟩,
        ⟨2383, true, false, [], [77107, 11]⟩,
        ⟨278, false, false, [361], []⟩,
        ⟨744, true, false, [361], [77107]⟩,
        ⟨2384, true, false, [], [77107]⟩
      ]⟩,
    ⟨[365], [363, 211], .source 247⟩,
    ⟨[367], [365, 199], .source 248⟩,
    ⟨[369], [367, 87], .source 249⟩,
    ⟨[371], [369, 107], .source 250⟩,
    ⟨[
      77475, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [371, 77225], .contexts [
        ⟨2385, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨295, false, false, [363], [1, 5, 3, 1]⟩,
        ⟨1491, false, false, [363], [5, 3, 1]⟩,
        ⟨2386, true, false, [], [77355, 5, 3, 1]⟩,
        ⟨1467, false, false, [365], [3, 1]⟩,
        ⟨2387, true, false, [], [77221, 3, 1]⟩,
        ⟨904, false, false, [367], [1]⟩,
        ⟨2388, true, false, [], [77221, 1]⟩,
        ⟨915, false, false, [369], []⟩,
        ⟨2389, true, false, [], [77225]⟩
      ]⟩,
    ⟨[373], [371, 109], .source 251⟩,
    ⟨[375], [373, 103], .source 252⟩,
    ⟨[377], [375, 109], .source 253⟩,
    ⟨[379], [377, 107], .source 254⟩,
    ⟨[77477, 9], [77477, 9], .contexts []⟩,
    ⟨[77477, 9], [379, 77361], .contexts [
        ⟨2395, false, false, [], []⟩,
        ⟨2297, true, false, [], [9]⟩,
        ⟨2297, true, false, [], [9]⟩,
        ⟨2295, true, false, [], [9]⟩,
        ⟨765, false, false, [77475], []⟩,
        ⟨774, false, false, [77475], []⟩,
        ⟨2390, false, false, [], [15, 13, 1, 11]⟩,
        ⟨878, false, false, [371], [13, 1, 11]⟩,
        ⟨2391, true, false, [], [77225, 13, 1, 11]⟩,
        ⟨869, false, false, [373], [1, 11]⟩,
        ⟨2392, true, false, [], [77225, 1, 11]⟩,
        ⟨611, false, false, [375], [11]⟩,
        ⟨917, false, false, [375], [11]⟩,
        ⟨2393, true, false, [], [77221, 11]⟩,
        ⟨1832, false, false, [377], []⟩,
        ⟨2394, true, false, [], [77361]⟩,
        ⟨1827, false, false, [379], []⟩
      ]⟩,
    ⟨[77477, 9], [379, 77361], .contexts [
        ⟨2396, false, false, [], []⟩,
        ⟨24, true, false, [], [379, 77361]⟩
      ]⟩,
    ⟨[381], [378], .source 255⟩,
    ⟨[77361, 9], [381, 77477], .contexts [
        ⟨2397, true, false, [378], [9]⟩,
        ⟨76, false, false, [378, 77477], []⟩,
        ⟨2398, true, false, [], [77477]⟩
      ]⟩,
    ⟨[379, 77361], [379, 77361], .contexts []⟩,
    ⟨[383], [379, 159], .source 256⟩,
    ⟨[383, 77361], [383, 77361], .contexts []⟩,
    ⟨[383, 77361], [383, 77361], .contexts []⟩,
    ⟨[77475, 9], [77475, 9], .contexts []⟩,
    ⟨[77475, 9], [383, 77361], .contexts [
        ⟨2404, false, false, [], []⟩,
        ⟨2296, true, false, [], [9]⟩,
        ⟨2296, true, false, [], [9]⟩,
        ⟨2296, true, false, [], [9]⟩,
        ⟨18, true, false, [77475], [9]⟩,
        ⟨2295, false, false, [], [1, 9]⟩,
        ⟨786, false, false, [77477], []⟩,
        ⟨788, false, false, [77477], []⟩,
        ⟨2395, false, false, [], [1, 9, 1]⟩,
        ⟨2397, false, false, [], [1, 9, 1]⟩,
        ⟨2400, false, false, [], [1, 9, 1]⟩,
        ⟨2400, false, false, [], [1, 9, 1]⟩,
        ⟨1821, false, false, [379], [9, 1]⟩,
        ⟨1114, false, false, [379], [1]⟩,
        ⟨2401, true, false, [], [77235, 1]⟩,
        ⟨1820, false, false, [383], []⟩,
        ⟨2402, false, false, [], []⟩,
        ⟨2403, false, false, [], []⟩,
        ⟨1827, false, false, [383], []⟩
      ]⟩,
    ⟨[77475, 9], [383, 77361], .contexts [
        ⟨2405, false, false, [], []⟩,
        ⟨24, true, false, [], [383, 77361]⟩
      ]⟩,
    ⟨[385], [382], .source 257⟩,
    ⟨[381, 77477], [381, 77477], .contexts []⟩,
    ⟨[387], [379, 385], .source 258⟩,
    ⟨[77475, 9], [383, 77361], .contexts [
        ⟨2404, false, false, [], []⟩,
        ⟨2406, false, false, [], []⟩,
        ⟨2402, false, false, [], []⟩,
        ⟨2403, false, false, [], []⟩,
        ⟨2403, false, false, [], []⟩
      ]⟩,
    ⟨[389], [383, 87], .source 259⟩,
    ⟨[77477], [387, 77475], .contexts [
        ⟨2408, true, false, [380], []⟩,
        ⟨2408, true, false, [380], []⟩,
        ⟨2399, true, false, [380], []⟩,
        ⟨2406, true, false, [380, 382], [9]⟩,
        ⟨76, false, false, [380, 382, 77475], []⟩,
        ⟨2407, true, false, [380], [77475]⟩,
        ⟨2398, false, true, [], [385, 77475]⟩,
        ⟨2409, true, false, [], [77475]⟩
      ]⟩,
    ⟨[391], [381, 387], .source 260⟩,
    ⟨[393], [389, 391], .source 261⟩,
    ⟨[9, 3, 9, 3], [], .contexts [
        ⟨305, false, false, [], []⟩
      ]⟩,
    ⟨[77475], [77475], .contexts []⟩,
    ⟨[77475, 3], [77475, 3], .contexts []⟩,
    ⟨[77475], [77475], .contexts []⟩,
    ⟨[395], [392], .source 262⟩,
    ⟨[392], [392], .contexts []⟩,
    ⟨[77475, 3], [395, 77475], .contexts [
        ⟨2417, false, false, [], []⟩,
        ⟨2414, false, false, [392], [77475, 3]⟩,
        ⟨2413, false, false, [392, 389], [77475, 3]⟩,
        ⟨2412, true, false, [392, 389, 381], [3]⟩,
        ⟨2399, true, false, [392, 389], [3]⟩,
        ⟨2411, false, false, [392], [77361, 9, 3]⟩,
        ⟨1081, false, false, [392, 383], [77361, 9, 3]⟩,
        ⟨1828, true, false, [392, 383], [9, 3]⟩,
        ⟨2410, true, false, [392], [3, 9, 3]⟩,
        ⟨2415, false, false, [392, 77475], []⟩,
        ⟨2416, false, false, [392], []⟩,
        ⟨2418, false, false, [392], []⟩,
        ⟨2420, true, false, [], [77475]⟩,
        ⟨2420, true, false, [], [77475]⟩,
        ⟨2419, true, false, [], [77475]⟩
      ]⟩,
    ⟨[397], [383, 111], .source 263⟩,
    ⟨[397, 77237], [397, 77237], .contexts []⟩,
    ⟨[397, 77237], [397, 77237], .contexts []⟩,
    ⟨[399], [396], .source 264⟩,
    ⟨[399], [396], .contexts [
        ⟨2425, false, false, [], []⟩
      ]⟩,
    ⟨[396], [396], .contexts []⟩,
    ⟨[77237, 5], [399, 77475], .contexts [
        ⟨2424, true, false, [396], [5]⟩,
        ⟨2423, true, false, [396], [5]⟩,
        ⟨1131, true, false, [], [5]⟩,
        ⟨2422, false, false, [396], [77113, 9, 5]⟩,
        ⟨1829, true, false, [396, 383], [9, 5]⟩,
        ⟨2410, true, false, [396], [5, 9, 5]⟩,
        ⟨892, false, false, [396, 77475], []⟩,
        ⟨2416, false, false, [396], []⟩,
        ⟨2418, false, false, [396], []⟩,
        ⟨2427, true, false, [], [77475]⟩,
        ⟨2427, true, false, [], [77475]⟩,
        ⟨2426, true, false, [], [77475]⟩
      ]⟩,
    ⟨[397], [397], .contexts []⟩,
    ⟨[397], [397], .contexts []⟩,
    ⟨[77473], [397, 77237], .contexts [
        ⟨2299, true, false, [], []⟩,
        ⟨2428, true, false, [398], [5]⟩,
        ⟨49, false, false, [398, 77237], []⟩,
        ⟨2425, false, true, [], [77237]⟩,
        ⟨2423, false, false, [], []⟩,
        ⟨2430, true, false, [], [77237]⟩,
        ⟨2429, true, false, [], [77237]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 038. -/
def y322TCContextRaw038 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77237, 3], [399, 77471], .contexts [
        ⟨2431, true, false, [396], [3]⟩,
        ⟨2290, false, false, [396], []⟩,
        ⟨2300, false, false, [396], []⟩,
        ⟨2427, true, false, [], [77471]⟩,
        ⟨2427, true, false, [], [77471]⟩,
        ⟨2426, true, false, [], [77471]⟩
      ]⟩,
    ⟨[407], [383, 109], .source 268⟩,
    ⟨[409], [407, 123], .source 269⟩,
    ⟨[411], [409, 107], .source 270⟩,
    ⟨[413], [411, 391], .source 271⟩,
    ⟨[413, 77475, 11], [77475], .contexts [
        ⟨2436, false, false, [], [77475, 11]⟩,
        ⟨2413, false, false, [411], [77475, 11]⟩,
        ⟨2412, true, false, [411, 381], [11]⟩,
        ⟨2399, true, false, [411], [11]⟩,
        ⟨2435, false, false, [], [77361, 9, 11]⟩,
        ⟨1832, true, false, [409], [9, 11]⟩,
        ⟨2434, false, false, [], [77221, 11, 9, 11]⟩,
        ⟨920, true, false, [407], [11, 9, 11]⟩,
        ⟨2433, false, false, [], [77221, 9, 11, 9, 11]⟩,
        ⟨1831, true, false, [383], [9, 11, 9, 11]⟩,
        ⟨2410, true, false, [], [11, 9, 11, 9, 11]⟩,
        ⟨965, false, false, [77475], []⟩,
        ⟨2416, false, false, [], []⟩
      ]⟩,
    ⟨[415], [412], .source 272⟩,
    ⟨[412], [412], .contexts []⟩,
    ⟨[417], [383, 285], .source 273⟩,
    ⟨[77213, 13], [77213, 13], .contexts []⟩,
    ⟨[419], [416], .source 274⟩,
    ⟨[416], [416], .contexts []⟩,
    ⟨[77213, 13], [419, 77475], .contexts [
        ⟨2441, false, false, [], []⟩,
        ⟨593, true, false, [], [13]⟩,
        ⟨2440, false, false, [416], [77215, 9, 13]⟩,
        ⟨1841, true, false, [416, 383], [9, 13]⟩,
        ⟨2410, true, false, [416], [13, 9, 13]⟩,
        ⟨828, false, false, [416, 77475], []⟩,
        ⟨2416, false, false, [416], []⟩,
        ⟨2418, false, false, [416], []⟩,
        ⟨2443, true, false, [], [77475]⟩,
        ⟨2443, true, false, [], [77475]⟩,
        ⟨2442, true, false, [], [77475]⟩
      ]⟩,
    ⟨[77475, 13], [417, 77213], .contexts [
        ⟨2444, true, false, [418], [13]⟩,
        ⟨98, false, false, [418, 77213], []⟩,
        ⟨2442, false, true, [], [77213]⟩
      ]⟩,
    ⟨[421], [407, 391], .source 275⟩,
    ⟨[423], [420], .source 276⟩,
    ⟨[420], [420], .contexts []⟩,
    ⟨[77475, 15], [423, 77475], .contexts [
        ⟨2446, false, false, [420], [77475, 15]⟩,
        ⟨2413, false, false, [420, 407], [77475, 15]⟩,
        ⟨2412, true, false, [420, 407, 381], [15]⟩,
        ⟨2399, true, false, [420, 407], [15]⟩,
        ⟨2433, false, false, [420], [77361, 9, 15]⟩,
        ⟨1834, true, false, [420, 383], [9, 15]⟩,
        ⟨2410, true, false, [420], [15, 9, 15]⟩,
        ⟨835, false, false, [420, 77475], []⟩,
        ⟨2416, false, false, [420], []⟩,
        ⟨2418, false, false, [420], []⟩,
        ⟨2448, true, false, [], [77475]⟩,
        ⟨2448, true, false, [], [77475]⟩,
        ⟨2447, true, false, [], [77475]⟩
      ]⟩,
    ⟨[77473], [397, 77237], .contexts [
        ⟨2431, false, false, [], []⟩,
        ⟨2424, false, false, [], []⟩
      ]⟩,
    ⟨[77473], [397, 77237], .contexts [
        ⟨2450, false, false, [], []⟩
      ]⟩,
    ⟨[395, 77475], [395, 77475], .contexts []⟩,
    ⟨[425], [395, 397], .source 277⟩,
    ⟨[427], [425, 399], .source 278⟩,
    ⟨[5, 3, 5], [2, 4, 2], .contexts [
        ⟨263, false, false, [], [2, 4, 2]⟩
      ]⟩,
    ⟨[77471, 5], [77471, 5], .contexts []⟩,
    ⟨[77471], [77471], .contexts []⟩,
    ⟨[429], [29, 399], .source 279⟩,
    ⟨[399, 77471], [399, 77471], .contexts []⟩,
    ⟨[77237, 3], [399, 77471], .contexts [
        ⟨2432, false, false, [], []⟩,
        ⟨2459, false, false, [], []⟩,
        ⟨2459, false, false, [], []⟩
      ]⟩,
    ⟨[77469, 3], [77469, 3], .contexts []⟩,
    ⟨[77469], [77469], .contexts []⟩,
    ⟨[431], [428], .source 280⟩,
    ⟨[433], [431, 399], .source 281⟩,
    ⟨[435], [31, 399], .source 282⟩,
    ⟨[77237, 2], [77237, 3], .contexts [
        ⟨36, false, false, [77237], []⟩
      ]⟩,
    ⟨[77471, 15], [77471, 15], .contexts []⟩,
    ⟨[437], [434], .source 283⟩,
    ⟨[439], [437, 399], .source 284⟩,
    ⟨[77471, 15], [439, 77471], .contexts [
        ⟨2467, false, false, [], []⟩,
        ⟨2465, false, false, [434], [77471, 15]⟩,
        ⟨740, false, false, [434], [399, 77471, 15]⟩,
        ⟨2432, true, false, [434, 13], [15]⟩,
        ⟨1164, true, false, [434], [3, 15]⟩,
        ⟨1893, false, false, [434, 77237], []⟩,
        ⟨2466, false, false, [434], []⟩,
        ⟨2460, false, false, [434], []⟩,
        ⟨2457, false, false, [434, 399], []⟩,
        ⟨2468, true, false, [], [399, 77471]⟩,
        ⟨2469, true, false, [], [77471]⟩
      ]⟩,
    ⟨[441], [243, 399], .source 285⟩,
    ⟨[77471, 11], [77471, 11], .contexts []⟩,
    ⟨[443], [440], .source 286⟩,
    ⟨[445], [443, 399], .source 287⟩,
    ⟨[77471, 11], [445, 77471], .contexts [
        ⟨2472, false, false, [], []⟩,
        ⟨2471, false, false, [440], [77471, 11]⟩,
        ⟨2432, true, false, [440, 243], [11]⟩,
        ⟨1610, true, false, [440], [3, 11]⟩,
        ⟨1040, false, false, [440, 77237], []⟩,
        ⟨2466, false, false, [440], []⟩,
        ⟨2460, false, false, [440], []⟩,
        ⟨2457, false, false, [440, 399], []⟩,
        ⟨2473, true, false, [], [399, 77471]⟩,
        ⟨2474, true, false, [], [77471]⟩
      ]⟩,
    ⟨[427, 77471], [427, 77471], .contexts []⟩,
    ⟨[77471, 5], [427, 77471], .contexts [
        ⟨2456, false, false, [], []⟩,
        ⟨2456, false, false, [], []⟩,
        ⟨2425, true, false, [397], [77471, 5]⟩,
        ⟨2432, true, false, [397], [5]⟩,
        ⟨2424, true, false, [], [3, 5]⟩,
        ⟨2424, true, false, [], [3, 5]⟩,
        ⟨2451, true, false, [], [3, 5]⟩,
        ⟨2298, true, false, [], [3, 5]⟩,
        ⟨2455, false, false, [77475], []⟩,
        ⟨266, false, false, [77475], []⟩,
        ⟨2417, false, false, [], [5, 3]⟩,
        ⟨2421, false, false, [], [5, 3]⟩,
        ⟨2452, false, false, [], [5, 3]⟩,
        ⟨2452, false, false, [], [5, 3]⟩,
        ⟨2293, false, false, [395], [3]⟩,
        ⟨2450, false, false, [395], [3]⟩,
        ⟨2453, true, false, [], [77237, 3]⟩,
        ⟨2432, false, false, [425], []⟩,
        ⟨2454, true, false, [], [77471]⟩,
        ⟨2457, false, false, [427], []⟩,
        ⟨24, true, false, [], [427, 77471]⟩,
        ⟨2476, false, false, [], []⟩
      ]⟩,
    ⟨[77471, 1], [77469], .contexts [
        ⟨2301, false, false, [], []⟩
      ]⟩,
    ⟨[77471, 1], [77469], .contexts [
        ⟨2478, false, false, [], []⟩,
        ⟨2302, false, false, [], []⟩,
        ⟨2285, false, false, [], []⟩,
        ⟨2285, false, false, [], []⟩
      ]⟩,
    ⟨[77471, 0], [77471, 1], .contexts [
        ⟨19, false, false, [77471], []⟩
      ]⟩,
    ⟨[447], [426], .source 288⟩,
    ⟨[426], [426], .contexts []⟩,
    ⟨[433, 77469], [433, 77469], .contexts []⟩,
    ⟨[77469, 3], [433, 77469], .contexts [
        ⟨2461, false, false, [], []⟩,
        ⟨2461, false, false, [], []⟩,
        ⟨2286, true, false, [], [3]⟩,
        ⟨2458, false, false, [428], [77471, 1, 3]⟩,
        ⟨744, false, false, [428], [399, 77471, 1, 3]⟩,
        ⟨2432, true, false, [428, 11], [1, 3]⟩,
        ⟨1160, true, false, [428], [3, 1, 3]⟩,
        ⟨852, false, false, [428, 77237], []⟩,
        ⟨853, false, false, [428, 77237], []⟩,
        ⟨2460, false, false, [428], [1]⟩,
        ⟨2286, false, false, [428, 399], []⟩,
        ⟨2462, false, false, [428, 399], []⟩,
        ⟨2463, true, false, [], [399, 77469]⟩,
        ⟨2464, true, false, [], [77469]⟩,
        ⟨2483, false, false, [], []⟩,
        ⟨2483, false, false, [], []⟩
      ]⟩,
    ⟨[433, 77467], [433, 77467], .contexts []⟩,
    ⟨[433, 77467], [433, 77467], .contexts []⟩,
    ⟨[433, 77467], [433, 77467], .contexts []⟩,
    ⟨[77467, 3], [77467, 3], .contexts []⟩,
    ⟨[77467], [77467], .contexts []⟩,
    ⟨[449], [432], .source 289⟩,
    ⟨[432], [432], .contexts []⟩,
    ⟨[77467, 3], [449, 77467], .contexts [
        ⟨2488, false, false, [], []⟩,
        ⟨2487, true, false, [432], [3]⟩,
        ⟨2486, true, false, [432], [3]⟩,
        ⟨2485, true, false, [432], [3]⟩,
        ⟨2283, true, false, [], [3]⟩,
        ⟨2484, true, false, [432], [15, 3]⟩,
        ⟨900, false, false, [432, 77469], []⟩,
        ⟨20, false, false, [432, 77469], []⟩,
        ⟨2303, false, false, [432], []⟩,
        ⟨2304, false, false, [432], []⟩,
        ⟨2282, false, false, [432], []⟩,
        ⟨2282, false, false, [432], []⟩,
        ⟨2489, false, false, [432], []⟩,
        ⟨2491, true, false, [], [77467]⟩,
        ⟨2491, true, false, [], [77467]⟩,
        ⟨2490, true, false, [], [77467]⟩
      ]⟩,
    ⟨[439, 77471], [439, 77471], .contexts []⟩,
    ⟨[77471, 15], [439, 77471], .contexts [
        ⟨2467, false, false, [], []⟩,
        ⟨2470, false, false, [], []⟩,
        ⟨2493, false, false, [], []⟩,
        ⟨2493, false, false, [], []⟩
      ]⟩,
    ⟨[439, 77467], [439, 77467], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 039. -/
def y322TCContextRaw039 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[439, 77467], [439, 77467], .contexts []⟩,
    ⟨[451], [438], .source 290⟩,
    ⟨[438], [438], .contexts []⟩,
    ⟨[77467, 1], [451, 77471], .contexts [
        ⟨2496, true, false, [438], [1]⟩,
        ⟨2495, true, false, [438], [1]⟩,
        ⟨2283, true, false, [], [1]⟩,
        ⟨2286, true, false, [], [15, 1]⟩,
        ⟨2494, true, false, [438], [1, 15, 1]⟩,
        ⟨911, false, false, [438, 77471], []⟩,
        ⟨2457, false, false, [438], []⟩,
        ⟨2498, true, false, [], [77471]⟩,
        ⟨2498, true, false, [], [77471]⟩,
        ⟨2497, true, false, [], [77471]⟩
      ]⟩,
    ⟨[439], [439], .contexts []⟩,
    ⟨[439], [439], .contexts []⟩,
    ⟨[77469], [439, 77467], .contexts [
        ⟨2479, true, false, [], []⟩,
        ⟨2499, true, false, [450], [1]⟩,
        ⟨18, false, false, [450, 77467], []⟩,
        ⟨2497, false, true, [], [77467]⟩,
        ⟨2495, false, false, [], []⟩,
        ⟨2501, true, false, [], [77467]⟩,
        ⟨2500, true, false, [], [77467]⟩
      ]⟩,
    ⟨[77469], [439, 77467], .contexts [
        ⟨2502, false, false, [], []⟩,
        ⟨2496, false, false, [], []⟩
      ]⟩,
    ⟨[453], [451, 447], .source 291⟩,
    ⟨[455], [453, 439], .source 292⟩,
    ⟨[77467, 5], [455, 77467], .contexts [
        ⟨2502, true, false, [438], [5]⟩,
        ⟨2286, true, false, [438], [5]⟩,
        ⟨2476, true, false, [438, 426], [1, 5]⟩,
        ⟨2477, true, false, [438, 426], [1, 5]⟩,
        ⟨1509, false, false, [438, 426, 77471], []⟩,
        ⟨2480, false, false, [438, 426], []⟩,
        ⟨2479, false, false, [438, 426], []⟩,
        ⟨2462, false, false, [438, 426], []⟩,
        ⟨2482, true, false, [438], [77469]⟩,
        ⟨2482, true, false, [438], [77469]⟩,
        ⟨2481, true, false, [438], [77469]⟩,
        ⟨2503, false, false, [438, 447], []⟩,
        ⟨2497, true, false, [], [447, 439, 77467]⟩,
        ⟨2504, true, false, [], [439, 77467]⟩,
        ⟨2505, true, false, [], [77467]⟩
      ]⟩,
    ⟨[445, 77471], [445, 77471], .contexts []⟩,
    ⟨[457], [445, 439], .source 293⟩,
    ⟨[77469], [439, 77467], .contexts [
        ⟨2503, false, false, [], []⟩
      ]⟩,
    ⟨[77471, 1], [439, 77467], .contexts [
        ⟨2478, false, false, [], []⟩,
        ⟨2509, false, false, [], []⟩,
        ⟨2496, false, false, [], []⟩,
        ⟨2496, false, false, [], []⟩
      ]⟩,
    ⟨[77467, 11], [77467, 11], .contexts []⟩,
    ⟨[459], [456], .source 294⟩,
    ⟨[461], [459, 439], .source 295⟩,
    ⟨[455, 77467], [455, 77467], .contexts []⟩,
    ⟨[77467, 13], [77465], .contexts [
        ⟨2305, false, false, [], []⟩,
        ⟨2306, false, false, [], []⟩,
        ⟨2278, false, false, [], []⟩,
        ⟨2278, false, false, [], []⟩
      ]⟩,
    ⟨[77467, 12], [77467, 13], .contexts [
        ⟨108, false, false, [77467], []⟩
      ]⟩,
    ⟨[77465, 5], [77465, 5], .contexts []⟩,
    ⟨[77465], [77465], .contexts []⟩,
    ⟨[463], [454], .source 296⟩,
    ⟨[454], [454], .contexts []⟩,
    ⟨[77465, 5], [463, 77465], .contexts [
        ⟨2517, false, false, [], []⟩,
        ⟨2279, true, false, [], [5]⟩,
        ⟨2514, true, false, [454], [13, 5]⟩,
        ⟨2514, true, false, [454], [13, 5]⟩,
        ⟨2506, true, false, [454], [13, 5]⟩,
        ⟨1578, false, false, [454, 77467], []⟩,
        ⟨2516, false, false, [454], []⟩,
        ⟨2515, false, false, [454], []⟩,
        ⟨2518, false, false, [454], []⟩,
        ⟨2520, true, false, [], [77465]⟩,
        ⟨2520, true, false, [], [77465]⟩,
        ⟨2519, true, false, [], [77465]⟩
      ]⟩,
    ⟨[449, 77467], [449, 77467], .contexts []⟩,
    ⟨[77465, 3], [77465, 3], .contexts []⟩,
    ⟨[448], [448], .contexts []⟩,
    ⟨[77465, 3], [433, 77465], .contexts [
        ⟨2523, false, false, [], []⟩,
        ⟨2279, true, false, [], [3]⟩,
        ⟨2522, true, false, [448], [13, 3]⟩,
        ⟨2522, true, false, [448], [13, 3]⟩,
        ⟨2492, true, false, [448], [13, 3]⟩,
        ⟨2488, true, false, [448], [13, 3]⟩,
        ⟨932, false, false, [448, 77467], []⟩,
        ⟨2516, false, false, [448], []⟩,
        ⟨2515, false, false, [448], []⟩,
        ⟨2518, false, false, [448], []⟩,
        ⟨2524, true, false, [], [77465]⟩,
        ⟨2524, true, false, [], [77465]⟩,
        ⟨2490, false, true, [], [77465]⟩
      ]⟩,
    ⟨[461, 77467], [461, 77467], .contexts []⟩,
    ⟨[77467, 11], [461, 77467], .contexts [
        ⟨2511, false, false, [], []⟩,
        ⟨2511, false, false, [], []⟩,
        ⟨2508, false, false, [456], [77467, 11]⟩,
        ⟨2503, true, false, [456, 445], [11]⟩,
        ⟨2286, true, false, [456, 445], [11]⟩,
        ⟨2507, true, false, [456], [1, 11]⟩,
        ⟨2507, true, false, [456], [1, 11]⟩,
        ⟨2475, true, false, [456], [1, 11]⟩,
        ⟨2472, true, false, [456], [1, 11]⟩,
        ⟨1000, false, false, [456, 77471], []⟩,
        ⟨2480, false, false, [456], []⟩,
        ⟨2510, false, false, [456], []⟩,
        ⟨2489, false, false, [456, 439], []⟩,
        ⟨2512, true, false, [], [439, 77467]⟩,
        ⟨2513, true, false, [], [77467]⟩,
        ⟨2526, false, false, [], []⟩,
        ⟨2526, false, false, [], []⟩
      ]⟩,
    ⟨[461, 77465], [461, 77465], .contexts []⟩,
    ⟨[461, 77465], [461, 77465], .contexts []⟩,
    ⟨[77465, 11], [77465, 11], .contexts []⟩,
    ⟨[461], [461], .contexts []⟩,
    ⟨[461], [461], .contexts []⟩,
    ⟨[461], [461], .contexts [
        ⟨24, false, false, [], [461]⟩,
        ⟨2531, false, false, [], []⟩,
        ⟨2532, false, false, [], []⟩
      ]⟩,
    ⟨[463, 77465], [463, 77465], .contexts []⟩,
    ⟨[77465, 5], [463, 77465], .contexts [
        ⟨2517, false, false, [], []⟩,
        ⟨2521, false, false, [], []⟩,
        ⟨2534, false, false, [], []⟩,
        ⟨2534, false, false, [], []⟩
      ]⟩,
    ⟨[77465, 1], [77463], .contexts [
        ⟨2307, false, false, [], []⟩
      ]⟩,
    ⟨[77465, 1], [77463], .contexts [
        ⟨2536, false, false, [], []⟩,
        ⟨2308, false, false, [], []⟩,
        ⟨2274, false, false, [], []⟩,
        ⟨2274, false, false, [], []⟩
      ]⟩,
    ⟨[77465, 0], [77465, 1], .contexts [
        ⟨19, false, false, [77465], []⟩
      ]⟩,
    ⟨[462], [462], .contexts []⟩,
    ⟨[77465, 11], [461, 77465], .contexts [
        ⟨2530, false, false, [], []⟩,
        ⟨2530, false, false, [], []⟩,
        ⟨2515, true, false, [], [11]⟩,
        ⟨137, false, false, [77467], []⟩,
        ⟨138, false, false, [77467], []⟩,
        ⟨2527, false, false, [], [13]⟩,
        ⟨2279, false, false, [461], []⟩,
        ⟨2528, false, false, [], []⟩,
        ⟨2529, false, false, [], []⟩,
        ⟨2518, false, false, [461], []⟩,
        ⟨2533, true, false, [], [77465]⟩,
        ⟨2528, false, false, [], []⟩,
        ⟨2529, false, false, [], []⟩,
        ⟨2529, false, false, [], []⟩
      ]⟩,
    ⟨[461, 77461], [461, 77461], .contexts []⟩,
    ⟨[461, 77461], [461, 77461], .contexts []⟩,
    ⟨[465], [460], .source 297⟩,
    ⟨[460], [460], .contexts []⟩,
    ⟨[77461, 1], [465, 77465], .contexts [
        ⟨2542, true, false, [460], [1]⟩,
        ⟨2541, true, false, [460], [1]⟩,
        ⟨2272, true, false, [], [1]⟩,
        ⟨2275, true, false, [], [11, 1]⟩,
        ⟨2540, true, false, [460], [1, 11, 1]⟩,
        ⟨1068, false, false, [460, 77465], []⟩,
        ⟨2518, false, false, [460], []⟩,
        ⟨2544, true, false, [], [77465]⟩,
        ⟨2544, true, false, [], [77465]⟩,
        ⟨2543, true, false, [], [77465]⟩
      ]⟩,
    ⟨[77463], [461, 77461], .contexts [
        ⟨2537, true, false, [], []⟩,
        ⟨2545, true, false, [464], [1]⟩,
        ⟨18, false, false, [464, 77461], []⟩,
        ⟨2543, false, true, [], [77461]⟩,
        ⟨2541, false, false, [], []⟩,
        ⟨2532, true, false, [], [77461]⟩,
        ⟨2531, true, false, [], [77461]⟩
      ]⟩,
    ⟨[77463], [461, 77461], .contexts [
        ⟨2546, false, false, [], []⟩,
        ⟨2542, false, false, [], []⟩
      ]⟩,
    ⟨[467], [465, 455], .source 298⟩,
    ⟨[469], [467, 461], .source 299⟩,
    ⟨[469, 77461], [469, 77461], .contexts []⟩,
    ⟨[77461, 5, 9], [469, 77461, 9], .contexts [
        ⟨2546, true, false, [460], [5, 9]⟩,
        ⟨2275, true, false, [460], [5, 9]⟩,
        ⟨2535, true, false, [460, 462], [1, 5, 9]⟩,
        ⟨1509, false, false, [460, 462, 77465], [9]⟩,
        ⟨2538, false, false, [460, 462], [9]⟩,
        ⟨2537, false, false, [460, 462], [9]⟩,
        ⟨2539, true, false, [460], [77463, 9]⟩,
        ⟨2539, true, false, [460], [77463, 9]⟩,
        ⟨2519, false, true, [460], [77463, 9]⟩,
        ⟨2547, false, false, [460, 455], [9]⟩,
        ⟨2543, true, false, [], [455, 461, 77461, 9]⟩,
        ⟨2548, true, false, [], [461, 77461, 9]⟩,
        ⟨2549, true, false, [], [77461, 9]⟩,
        ⟨2550, false, false, [], [9]⟩,
        ⟨2550, false, false, [], [9]⟩
      ]⟩,
    ⟨[77461, 9], [77459], .contexts [
        ⟨2310, false, false, [], []⟩,
        ⟨2311, false, false, [], []⟩,
        ⟨2268, false, false, [], []⟩,
        ⟨2268, false, false, [], []⟩
      ]⟩,
    ⟨[77459, 5], [77459, 5], .contexts []⟩,
    ⟨[77459], [77459], .contexts []⟩,
    ⟨[471], [468], .source 300⟩,
    ⟨[471], [471], .contexts []⟩,
    ⟨[468], [468], .contexts []⟩,
    ⟨[471, 77459], [471, 77459], .contexts []⟩,
    ⟨[77459, 5, 1], [471, 77457], .contexts [
        ⟨2553, false, false, [], [1]⟩,
        ⟨2553, false, false, [], [1]⟩,
        ⟨2269, true, false, [], [5, 1]⟩,
        ⟨2551, true, false, [468], [5, 1]⟩,
        ⟨1672, false, false, [468, 77461], [1]⟩,
        ⟨77, false, false, [468, 77461], [1]⟩,
        ⟨2552, false, false, [468], [1]⟩,
        ⟨2554, false, false, [468], [1]⟩,
        ⟨2557, true, false, [], [77459, 1]⟩,
        ⟨2557, true, false, [], [77459, 1]⟩,
        ⟨2555, true, false, [], [77459, 1]⟩,
        ⟨2556, true, false, [], [77459, 1]⟩,
        ⟨2558, false, false, [], [1]⟩,
        ⟨2558, false, false, [], [1]⟩,
        ⟨2266, false, false, [471], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 040. -/
def y322TCContextRaw040 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[471, 77455], [471, 77455], .contexts []⟩,
    ⟨[471, 77455], [471, 77455], .contexts []⟩,
    ⟨[77455, 1], [77455, 1], .contexts []⟩,
    ⟨[470], [470], .contexts []⟩,
    ⟨[77455, 1], [469, 77459], .contexts [
        ⟨2562, false, false, [], []⟩,
        ⟨2561, true, false, [470], [1]⟩,
        ⟨2560, true, false, [470], [1]⟩,
        ⟨2263, true, false, [], [1]⟩,
        ⟨2559, true, false, [470], [5, 1]⟩,
        ⟨1485, false, false, [470, 77459], []⟩,
        ⟨2554, false, false, [470], []⟩,
        ⟨2563, true, false, [], [77459]⟩,
        ⟨2563, true, false, [], [77459]⟩,
        ⟨2555, false, true, [], [77459]⟩
      ]⟩,
    ⟨[77479], [77355, 7], .source 38804⟩,
    ⟨[77355, 7], [77479], .contexts [
        ⟨2565, true, false, [], []⟩
      ]⟩,
    ⟨[77479], [77479], .contexts []⟩,
    ⟨[77355, 7], [77479], .contexts [
        ⟨2566, false, false, [], []⟩,
        ⟨2567, false, false, [], []⟩,
        ⟨2567, false, false, [], []⟩
      ]⟩,
    ⟨[209, 77109], [209, 77109], .contexts []⟩,
    ⟨[77355, 1], [209, 77109], .contexts [
        ⟨1493, false, false, [], []⟩,
        ⟨2569, false, false, [], []⟩,
        ⟨2569, false, false, [], []⟩
      ]⟩,
    ⟨[209], [209], .contexts [
        ⟨24, false, false, [], [209]⟩
      ]⟩,
    ⟨[77479, 1], [209, 77359], .contexts [
        ⟨2568, true, false, [], [1]⟩,
        ⟨1764, false, false, [77355], []⟩,
        ⟨1765, false, false, [77355], []⟩,
        ⟨2570, false, false, [], [7]⟩,
        ⟨1812, true, false, [209], [7]⟩,
        ⟨62, false, false, [209, 77359], []⟩,
        ⟨1796, false, false, [209], []⟩,
        ⟨1802, false, false, [209], []⟩,
        ⟨2571, true, false, [], [77359]⟩
      ]⟩,
    ⟨[77479], [77479], .contexts []⟩,
    ⟨[7, 9], [8, 6], .contexts [
        ⟨1017, false, false, [], [8, 6]⟩
      ]⟩,
    ⟨[8, 6], [9, 7], .contexts [
        ⟨77, false, false, [], [6]⟩,
        ⟨63, false, false, [9], []⟩
      ]⟩,
    ⟨[217], [217], .contexts [
        ⟨24, false, false, [], [217]⟩
      ]⟩,
    ⟨[77481], [77355, 13], .source 38805⟩,
    ⟨[77355, 13], [77481], .contexts [
        ⟨2577, true, false, [], []⟩
      ]⟩,
    ⟨[77481], [77481], .contexts []⟩,
    ⟨[77355, 13], [77481], .contexts [
        ⟨2578, false, false, [], []⟩,
        ⟨2579, false, false, [], []⟩,
        ⟨2579, false, false, [], []⟩
      ]⟩,
    ⟨[477], [209, 19], .source 303⟩,
    ⟨[479], [477, 211], .source 304⟩,
    ⟨[479, 77481], [479, 77481], .contexts []⟩,
    ⟨[479, 77481], [479, 77481], .contexts []⟩,
    ⟨[77481, 1], [77481, 1], .contexts []⟩,
    ⟨[77481], [77481], .contexts []⟩,
    ⟨[479], [479], .contexts [
        ⟨24, false, false, [], [479]⟩
      ]⟩,
    ⟨[77481, 1], [479, 77481], .contexts [
        ⟨2585, false, false, [], []⟩,
        ⟨2580, true, false, [], [1]⟩,
        ⟨387, false, false, [77355], []⟩,
        ⟨390, false, false, [77355], []⟩,
        ⟨2570, false, false, [], [13, 1, 13]⟩,
        ⟨318, false, false, [209], [1, 13]⟩,
        ⟨735, true, false, [209], [77109, 1, 13]⟩,
        ⟨2581, true, false, [], [77109, 1, 13]⟩,
        ⟨1491, false, false, [477], [13]⟩,
        ⟨2582, true, false, [], [77355, 13]⟩,
        ⟨2578, false, false, [479], []⟩,
        ⟨2583, false, false, [], []⟩,
        ⟨2584, false, false, [], []⟩,
        ⟨2586, false, false, [479], []⟩,
        ⟨2587, true, false, [], [77481]⟩
      ]⟩,
    ⟨[253, 77349], [253, 77349], .contexts []⟩,
    ⟨[253, 77347], [253, 77347], .contexts []⟩,
    ⟨[253, 77347], [253, 77347], .contexts []⟩,
    ⟨[77481, 3], [77481, 3], .contexts []⟩,
    ⟨[77481, 3], [253, 77347], .contexts [
        ⟨2592, false, false, [], []⟩,
        ⟨2580, true, false, [], [3]⟩,
        ⟨107, false, false, [77355], []⟩,
        ⟨109, false, false, [77355], []⟩,
        ⟨1470, false, false, [], [13]⟩,
        ⟨1563, false, false, [], [13]⟩,
        ⟨2589, false, false, [], [13]⟩,
        ⟨2589, false, false, [], [13]⟩,
        ⟨1346, false, false, [253], []⟩,
        ⟨2590, false, false, [], []⟩,
        ⟨2591, false, false, [], []⟩,
        ⟨1581, false, false, [253], []⟩,
        ⟨24, true, false, [], [253, 77347]⟩
      ]⟩,
    ⟨[481], [252], .source 305⟩,
    ⟨[483], [199, 135], .source 306⟩,
    ⟨[77481, 5], [77481, 5], .contexts []⟩,
    ⟨[77217], [77217], .contexts []⟩,
    ⟨[77481, 5], [483, 77217], .contexts [
        ⟨2596, false, false, [], []⟩,
        ⟨2580, true, false, [], [5]⟩,
        ⟨116, false, false, [77355], []⟩,
        ⟨117, false, false, [77355], []⟩,
        ⟨1473, false, false, [], [13]⟩,
        ⟨604, false, false, [199], []⟩,
        ⟨954, false, false, [199], []⟩,
        ⟨2595, true, false, [], [77217]⟩,
        ⟨2597, false, false, [483], []⟩,
        ⟨24, true, false, [], [483, 77217]⟩
      ]⟩,
    ⟨[485], [482], .source 307⟩,
    ⟨[217, 77481], [217, 77481], .contexts []⟩,
    ⟨[217, 77481], [217, 77481], .contexts []⟩,
    ⟨[77481, 9], [77481, 9], .contexts []⟩,
    ⟨[77481, 9], [217, 77481], .contexts [
        ⟨2602, false, false, [], []⟩,
        ⟨2580, true, false, [], [9]⟩,
        ⟨130, false, false, [77355], []⟩,
        ⟨131, false, false, [77355], []⟩,
        ⟨1528, false, false, [], [13]⟩,
        ⟨2578, false, false, [217], []⟩,
        ⟨2600, false, false, [], []⟩,
        ⟨2601, false, false, [], []⟩,
        ⟨2586, false, false, [217], []⟩,
        ⟨2576, true, false, [], [77481]⟩
      ]⟩,
    ⟨[209, 77115], [209, 77115], .contexts []⟩,
    ⟨[209, 77115], [209, 77115], .contexts []⟩,
    ⟨[77481, 11], [77481, 11], .contexts []⟩,
    ⟨[77481, 11], [209, 77115], .contexts [
        ⟨2606, false, false, [], []⟩,
        ⟨2580, true, false, [], [11]⟩,
        ⟨137, false, false, [77355], []⟩,
        ⟨138, false, false, [77355], []⟩,
        ⟨1535, false, false, [], [13]⟩,
        ⟨374, false, false, [209], []⟩,
        ⟨2604, false, false, [], []⟩,
        ⟨2605, false, false, [], []⟩,
        ⟨392, false, false, [209], []⟩,
        ⟨2571, true, false, [], [77115]⟩
      ]⟩,
    ⟨[77115, 11], [211, 77481], .contexts [
        ⟨2607, true, false, [208], [11]⟩,
        ⟨90, false, false, [208, 77481], []⟩,
        ⟨1489, true, false, [], [77481]⟩
      ]⟩,
    ⟨[77481, 1], [479, 77481], .contexts [
        ⟨2585, false, false, [], []⟩,
        ⟨2588, false, false, [], []⟩,
        ⟨2583, false, false, [], []⟩,
        ⟨2584, false, false, [], []⟩,
        ⟨2584, false, false, [], []⟩
      ]⟩,
    ⟨[487], [479, 253], .source 308⟩,
    ⟨[77345, 3], [77345, 3], .contexts []⟩,
    ⟨[489], [486], .source 309⟩,
    ⟨[491], [489, 253], .source 310⟩,
    ⟨[77345, 3], [491, 77345], .contexts [
        ⟨2611, false, false, [], []⟩,
        ⟨1342, true, false, [], [3]⟩,
        ⟨2610, false, false, [486], [77347, 1, 3]⟩,
        ⟨2593, true, false, [486, 479], [1, 3]⟩,
        ⟨2609, true, false, [486], [3, 1, 3]⟩,
        ⟨852, false, false, [486, 77481], []⟩,
        ⟨853, false, false, [486, 77481], []⟩,
        ⟨2592, false, false, [486], [1]⟩,
        ⟨2593, false, false, [486], [1]⟩,
        ⟨2590, false, false, [486], [1]⟩,
        ⟨2591, false, false, [486], [1]⟩,
        ⟨2591, false, false, [486], [1]⟩,
        ⟨1342, false, false, [486, 253], []⟩,
        ⟨1589, false, false, [486, 253], []⟩,
        ⟨2612, true, false, [], [253, 77345]⟩,
        ⟨2613, true, false, [], [77345]⟩
      ]⟩,
    ⟨[491, 77345], [491, 77345], .contexts []⟩,
    ⟨[77343, 3], [77343, 3], .contexts []⟩,
    ⟨[493], [490], .source 311⟩,
    ⟨[490], [490], .contexts []⟩,
    ⟨[77343, 3], [493, 77343], .contexts [
        ⟨2616, false, false, [], []⟩,
        ⟨1338, true, false, [], [3]⟩,
        ⟨2615, true, false, [490], [11, 3]⟩,
        ⟨2615, true, false, [490], [11, 3]⟩,
        ⟨2614, true, false, [490], [11, 3]⟩,
        ⟨2611, true, false, [490], [11, 3]⟩,
        ⟨976, false, false, [490, 77345], []⟩,
        ⟨1625, false, false, [490], []⟩,
        ⟨1623, false, false, [490], []⟩,
        ⟨1627, false, false, [490], []⟩,
        ⟨2618, true, false, [], [77343]⟩,
        ⟨2618, true, false, [], [77343]⟩,
        ⟨2617, true, false, [], [77343]⟩
      ]⟩,
    ⟨[493, 77343], [493, 77343], .contexts []⟩,
    ⟨[77341, 3], [77341, 3], .contexts []⟩,
    ⟨[492], [492], .contexts []⟩,
    ⟨[77341, 3], [491, 77341], .contexts [
        ⟨2621, false, false, [], []⟩,
        ⟨1334, true, false, [], [3]⟩,
        ⟨2620, true, false, [492], [9, 3]⟩,
        ⟨2620, true, false, [492], [9, 3]⟩,
        ⟨2619, true, false, [492], [9, 3]⟩,
        ⟨2616, true, false, [492], [9, 3]⟩,
        ⟨1010, false, false, [492, 77343], []⟩,
        ⟨1651, false, false, [492], []⟩,
        ⟨1649, false, false, [492], []⟩,
        ⟨1653, false, false, [492], []⟩,
        ⟨2622, true, false, [], [77341]⟩,
        ⟨2622, true, false, [], [77341]⟩,
        ⟨2617, false, true, [], [77341]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 041. -/
def y322TCContextRaw041 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[491, 77341], [491, 77341], .contexts []⟩,
    ⟨[77341, 3], [491, 77341], .contexts [
        ⟨2621, false, false, [], []⟩,
        ⟨2623, false, false, [], []⟩,
        ⟨2624, false, false, [], []⟩,
        ⟨2624, false, false, [], []⟩
      ]⟩,
    ⟨[77339], [261, 77337], .contexts [
        ⟨1329, true, false, [], []⟩,
        ⟨1329, true, false, [], []⟩,
        ⟨1372, true, false, [], []⟩,
        ⟨1702, true, false, [], []⟩,
        ⟨1701, true, false, [266], [1]⟩,
        ⟨18, false, false, [266, 77337], []⟩,
        ⟨1617, true, false, [], [77337]⟩,
        ⟨1699, false, false, [], []⟩,
        ⟨1704, true, false, [], [77337]⟩,
        ⟨1703, true, false, [], [77337]⟩,
        ⟨1618, true, false, [], [77337]⟩,
        ⟨1700, false, false, [], []⟩
      ]⟩,
    ⟨[495], [491, 261], .source 312⟩,
    ⟨[77339], [261, 77337], .contexts [
        ⟨2626, false, false, [], []⟩
      ]⟩,
    ⟨[77337], [77337], .contexts []⟩,
    ⟨[497], [494], .source 313⟩,
    ⟨[499], [497, 261], .source 314⟩,
    ⟨[77333, 3], [499, 77337], .contexts [
        ⟨1321, true, false, [], [3]⟩,
        ⟨1324, true, false, [], [1, 3]⟩,
        ⟨2627, false, false, [494], [77337, 3, 1, 3]⟩,
        ⟨2626, true, false, [494, 491], [3, 1, 3]⟩,
        ⟨1330, true, false, [494, 491], [3, 1, 3]⟩,
        ⟨2625, true, false, [494], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [494, 77341], []⟩,
        ⟨19, false, false, [494, 77341], []⟩,
        ⟨1702, false, false, [494], []⟩,
        ⟨2628, false, false, [494], []⟩,
        ⟨1700, false, false, [494], []⟩,
        ⟨1700, false, false, [494], []⟩,
        ⟨2629, false, false, [494, 261], []⟩,
        ⟨2630, true, false, [], [261, 77337]⟩,
        ⟨2631, true, false, [], [77337]⟩
      ]⟩,
    ⟨[501], [498], .source 315⟩,
    ⟨[77337, 3], [77335], .contexts [
        ⟨1373, false, false, [], []⟩
      ]⟩,
    ⟨[501], [501], .contexts []⟩,
    ⟨[501], [501], .contexts []⟩,
    ⟨[501], [501], .contexts []⟩,
    ⟨[77333, 15], [77331], .contexts [
        ⟨1375, false, false, [], []⟩,
        ⟨1376, false, false, [], []⟩,
        ⟨1316, false, false, [], []⟩,
        ⟨1316, false, false, [], []⟩
      ]⟩,
    ⟨[501, 77333], [501, 77333], .contexts []⟩,
    ⟨[77335], [501, 77333], .contexts [
        ⟨1323, true, false, [], []⟩,
        ⟨1323, true, false, [], []⟩,
        ⟨1374, true, false, [], []⟩,
        ⟨2634, true, false, [], []⟩,
        ⟨2632, true, false, [498], [3]⟩,
        ⟨35, false, false, [498, 77333], []⟩,
        ⟨2633, true, false, [], [77333]⟩,
        ⟨2637, true, false, [], [77333]⟩,
        ⟨2636, true, false, [], [77333]⟩,
        ⟨2635, true, false, [], [77333]⟩,
        ⟨2639, false, false, [], []⟩
      ]⟩,
    ⟨[77335], [501, 77333], .contexts [
        ⟨2640, false, false, [], []⟩
      ]⟩,
    ⟨[501, 77331], [501, 77331], .contexts []⟩,
    ⟨[501, 77331], [501, 77331], .contexts []⟩,
    ⟨[77331, 1], [77331, 1], .contexts []⟩,
    ⟨[77331], [77331], .contexts []⟩,
    ⟨[77331, 1], [501, 77331], .contexts [
        ⟨2644, false, false, [], []⟩,
        ⟨2638, true, false, [], [1]⟩,
        ⟨17, false, false, [77333], []⟩,
        ⟨21, false, false, [77333], []⟩,
        ⟨1319, false, false, [], [15]⟩,
        ⟨2641, false, false, [], [15]⟩,
        ⟨2639, false, false, [], [15]⟩,
        ⟨2639, false, false, [], [15]⟩,
        ⟨1317, false, false, [501], []⟩,
        ⟨2642, false, false, [], []⟩,
        ⟨2643, false, false, [], []⟩,
        ⟨2645, false, false, [501], []⟩,
        ⟨2637, true, false, [], [77331]⟩,
        ⟨2636, true, false, [], [77331]⟩,
        ⟨24, true, false, [], [501, 77331]⟩
      ]⟩,
    ⟨[77327, 13], [77327, 13], .contexts []⟩,
    ⟨[77327], [77327], .contexts []⟩,
    ⟨[500], [500], .contexts []⟩,
    ⟨[499], [500], .contexts [
        ⟨2633, true, true, [], []⟩,
        ⟨2649, false, false, [], []⟩,
        ⟨2649, false, false, [], []⟩
      ]⟩,
    ⟨[77327, 13], [499, 77327], .contexts [
        ⟨2647, false, false, [], []⟩,
        ⟨1309, true, false, [], [13]⟩,
        ⟨1313, true, false, [], [1, 13]⟩,
        ⟨2643, true, false, [500], [13, 1, 13]⟩,
        ⟨2643, true, false, [500], [13, 1, 13]⟩,
        ⟨2642, true, false, [500], [13, 1, 13]⟩,
        ⟨2646, true, false, [500], [13, 1, 13]⟩,
        ⟨2644, true, false, [500], [13, 1, 13]⟩,
        ⟨1587, false, false, [500, 77331], []⟩,
        ⟨190, false, false, [500, 77331], []⟩,
        ⟨1378, false, false, [500], [1]⟩,
        ⟨1379, false, false, [500], [1]⟩,
        ⟨1312, false, false, [500], [1]⟩,
        ⟨1312, false, false, [500], [1]⟩,
        ⟨1380, false, false, [500], []⟩,
        ⟨1381, false, false, [500], []⟩,
        ⟨1308, false, false, [500], []⟩,
        ⟨1308, false, false, [500], []⟩,
        ⟨2648, false, false, [500], []⟩,
        ⟨2650, true, false, [], [77327]⟩
      ]⟩,
    ⟨[499, 77327], [499, 77327], .contexts []⟩,
    ⟨[77327, 13], [499, 77327], .contexts [
        ⟨2647, false, false, [], []⟩,
        ⟨2651, false, false, [], []⟩,
        ⟨2652, false, false, [], []⟩,
        ⟨2652, false, false, [], []⟩
      ]⟩,
    ⟨[77325, 13], [77325, 13], .contexts []⟩,
    ⟨[77325], [77325], .contexts []⟩,
    ⟨[498], [498], .contexts []⟩,
    ⟨[77325, 13], [501, 77325], .contexts [
        ⟨2654, false, false, [], []⟩,
        ⟨1305, true, false, [], [13]⟩,
        ⟨2653, true, false, [498], [11, 13]⟩,
        ⟨1624, false, false, [498, 77327], []⟩,
        ⟨91, false, false, [498, 77327], []⟩,
        ⟨1382, false, false, [498], []⟩,
        ⟨1383, false, false, [498], []⟩,
        ⟨1304, false, false, [498], []⟩,
        ⟨1304, false, false, [498], []⟩,
        ⟨2655, false, false, [498], []⟩,
        ⟨2656, true, false, [], [77325]⟩,
        ⟨2656, true, false, [], [77325]⟩,
        ⟨2633, true, false, [], [77325]⟩,
        ⟨2635, true, false, [], [77325]⟩
      ]⟩,
    ⟨[501, 77325], [501, 77325], .contexts []⟩,
    ⟨[77325, 9], [77323], .contexts [
        ⟨1384, false, false, [], []⟩,
        ⟨1385, false, false, [], []⟩,
        ⟨1300, false, false, [], []⟩,
        ⟨1300, false, false, [], []⟩
      ]⟩,
    ⟨[77325, 8], [77325, 9], .contexts [
        ⟨77, false, false, [77325], []⟩
      ]⟩,
    ⟨[77323], [77323], .contexts []⟩,
    ⟨[77483], [77359, 11], .source 38806⟩,
    ⟨[77359, 11], [77483], .contexts [
        ⟨2662, true, false, [], []⟩
      ]⟩,
    ⟨[77483], [77483], .contexts []⟩,
    ⟨[77483], [77483], .contexts []⟩,
    ⟨[77359, 11], [77483], .contexts [
        ⟨2663, false, false, [], []⟩,
        ⟨2664, false, false, [], []⟩,
        ⟨2665, false, false, [], []⟩,
        ⟨2665, false, false, [], []⟩
      ]⟩,
    ⟨[77483], [77483], .contexts []⟩,
    ⟨[77359, 9, 11, 9], [11, 77359], .contexts [
        ⟨1795, true, false, [], [9, 11, 9]⟩,
        ⟨76, false, false, [77357], [11, 9]⟩,
        ⟨1762, false, false, [], [11, 9]⟩,
        ⟨1761, false, false, [], [11, 9]⟩,
        ⟨1762, false, false, [], [11, 9]⟩,
        ⟨1762, false, false, [], [11, 9]⟩,
        ⟨1763, true, false, [], [11, 9]⟩,
        ⟨1781, false, false, [77107], [9]⟩,
        ⟨1782, false, false, [77107], [9]⟩,
        ⟨277, false, false, [], [7, 9]⟩,
        ⟨338, false, false, [], [7, 9]⟩,
        ⟨271, false, false, [], [7, 9]⟩,
        ⟨272, false, false, [], [7, 9]⟩,
        ⟨272, false, false, [], [7, 9]⟩,
        ⟨1760, false, false, [11], [9]⟩,
        ⟨1779, false, false, [], [9]⟩,
        ⟨1780, false, false, [], [9]⟩,
        ⟨1766, false, false, [11], [9]⟩,
        ⟨94, true, false, [], [77357, 9]⟩,
        ⟨1779, false, false, [], [9]⟩,
        ⟨1780, false, false, [], [9]⟩,
        ⟨1780, false, false, [], [9]⟩,
        ⟨1795, false, false, [11], []⟩
      ]⟩,
    ⟨[11, 77483], [11, 77483], .contexts []⟩,
    ⟨[11, 77483], [11, 77483], .contexts []⟩,
    ⟨[77483, 9], [11, 77483], .contexts [
        ⟨2666, true, false, [], [9]⟩,
        ⟨344, false, false, [77359], []⟩,
        ⟨346, false, false, [77359], []⟩,
        ⟨2668, false, false, [], [11]⟩,
        ⟨2663, false, false, [11], []⟩,
        ⟨2669, false, false, [], []⟩,
        ⟨2670, false, false, [], []⟩,
        ⟨2667, false, false, [11], []⟩,
        ⟨94, true, false, [], [77483]⟩
      ]⟩,
    ⟨[1, 77483], [1, 77483], .contexts []⟩,
    ⟨[1, 77483], [1, 77483], .contexts []⟩,
    ⟨[77485], [77349, 11], .source 38807⟩,
    ⟨[77349, 11], [77485], .contexts [
        ⟨2674, true, false, [], []⟩
      ]⟩,
    ⟨[77485, 11], [77349], .contexts [
        ⟨2675, true, false, [], [11]⟩,
        ⟨90, false, false, [77349], []⟩,
        ⟨1349, false, false, [], []⟩
      ]⟩,
    ⟨[77485], [77485], .contexts []⟩,
    ⟨[77485], [77485], .contexts []⟩,
    ⟨[77349, 11], [77485], .contexts [
        ⟨2675, false, false, [], []⟩,
        ⟨2677, false, false, [], []⟩,
        ⟨2678, false, false, [], []⟩,
        ⟨2678, false, false, [], []⟩
      ]⟩,
    ⟨[257, 77485], [257, 77485], .contexts []⟩,
    ⟨[257, 77485], [257, 77485], .contexts []⟩,
    ⟨[77485, 1], [77485, 1], .contexts []⟩,
    ⟨[77485], [77485], .contexts []⟩,
    ⟨[257], [257], .contexts [
        ⟨24, false, false, [], [257]⟩
      ]⟩,
    ⟨[77485, 1], [257, 77485], .contexts [
        ⟨2682, false, false, [], []⟩,
        ⟨2679, true, false, [], [1]⟩,
        ⟨992, false, false, [77349], []⟩,
        ⟨993, false, false, [77349], []⟩,
        ⟨1586, false, false, [], [11]⟩,
        ⟨2675, false, false, [257], []⟩,
        ⟨2680, false, false, [], []⟩,
        ⟨2681, false, false, [], []⟩,
        ⟨2683, false, false, [257], []⟩,
        ⟨2684, true, false, [], [77485]⟩
      ]⟩,
    ⟨[249, 77355], [249, 77355], .contexts []⟩,
    ⟨[503], [249, 209], .source 316⟩]

/-- Exact literal claimed equations and contextual derivations, block 042. -/
def y322TCContextRaw042 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77485, 3], [77485, 3], .contexts []⟩,
    ⟨[503], [503], .contexts [
        ⟨24, false, false, [], [503]⟩
      ]⟩,
    ⟨[77485, 3], [503, 77113], .contexts [
        ⟨2688, false, false, [], []⟩,
        ⟨2679, true, false, [], [3]⟩,
        ⟨335, false, false, [77349], []⟩,
        ⟨336, false, false, [77349], []⟩,
        ⟨1556, false, false, [], [11]⟩,
        ⟨1559, false, false, [], [11]⟩,
        ⟨2686, false, false, [], [11]⟩,
        ⟨2686, false, false, [], [11]⟩,
        ⟨1525, false, false, [249], []⟩,
        ⟨2687, true, false, [], [77113]⟩,
        ⟨371, false, false, [503], []⟩,
        ⟨2689, true, false, [], [77113]⟩
      ]⟩,
    ⟨[505], [502], .source 317⟩,
    ⟨[77113, 3], [505, 77485], .contexts [
        ⟨2690, true, false, [502], [3]⟩,
        ⟨35, false, false, [502, 77485], []⟩,
        ⟨2691, true, false, [], [77485]⟩
      ]⟩,
    ⟨[261, 77485], [261, 77485], .contexts []⟩,
    ⟨[261, 77485], [261, 77485], .contexts []⟩,
    ⟨[77485, 5], [77485, 5], .contexts []⟩,
    ⟨[261], [261], .contexts [
        ⟨24, false, false, [], [261]⟩,
        ⟨1703, false, false, [], []⟩,
        ⟨1704, false, false, [], []⟩
      ]⟩,
    ⟨[77485, 5], [261, 77485], .contexts [
        ⟨2695, false, false, [], []⟩,
        ⟨2679, true, false, [], [5]⟩,
        ⟨1083, false, false, [77349], []⟩,
        ⟨1084, false, false, [77349], []⟩,
        ⟨1576, false, false, [], [11]⟩,
        ⟨2675, false, false, [261], []⟩,
        ⟨2693, false, false, [], []⟩,
        ⟨2694, false, false, [], []⟩,
        ⟨2683, false, false, [261], []⟩,
        ⟨2696, true, false, [], [77485]⟩
      ]⟩,
    ⟨[251, 77485], [251, 77485], .contexts []⟩,
    ⟨[251, 77485], [251, 77485], .contexts []⟩,
    ⟨[77485, 15], [77485, 15], .contexts []⟩,
    ⟨[251], [251], .contexts [
        ⟨24, false, false, [], [251]⟩
      ]⟩,
    ⟨[77485, 15], [251, 77485], .contexts [
        ⟨2700, false, false, [], []⟩,
        ⟨2679, true, false, [], [15]⟩,
        ⟨358, false, false, [77349], []⟩,
        ⟨359, false, false, [77349], []⟩,
        ⟨1348, false, false, [], [11]⟩,
        ⟨1568, false, false, [], [11]⟩,
        ⟨1567, false, false, [], [11]⟩,
        ⟨1567, false, false, [], [11]⟩,
        ⟨2675, false, false, [251], []⟩,
        ⟨2698, false, false, [], []⟩,
        ⟨2699, false, false, [], []⟩,
        ⟨2683, false, false, [251], []⟩,
        ⟨2701, true, false, [], [77485]⟩
      ]⟩,
    ⟨[503, 77113], [503, 77113], .contexts []⟩,
    ⟨[77485, 3], [503, 77113], .contexts [
        ⟨2688, false, false, [], []⟩,
        ⟨2690, false, false, [], []⟩,
        ⟨2703, false, false, [], []⟩,
        ⟨2703, false, false, [], []⟩
      ]⟩,
    ⟨[507], [503, 399], .source 318⟩,
    ⟨[3, 9, 3, 9], [], .contexts [
        ⟨1009, false, false, [], []⟩
      ]⟩,
    ⟨[77471, 9], [77471, 9], .contexts []⟩,
    ⟨[509], [506], .source 319⟩,
    ⟨[506], [506], .contexts []⟩,
    ⟨[77471, 9], [509, 77485], .contexts [
        ⟨2707, false, false, [], []⟩,
        ⟨2705, false, false, [506], [77471, 9]⟩,
        ⟨2432, true, false, [506, 503], [9]⟩,
        ⟨1131, true, false, [506, 503], [3, 9]⟩,
        ⟨2704, true, false, [506], [9, 3, 9]⟩,
        ⟨2706, false, false, [506, 77485], []⟩,
        ⟨2683, false, false, [506], []⟩,
        ⟨2709, true, false, [], [77485]⟩,
        ⟨2709, true, false, [], [77485]⟩,
        ⟨2708, true, false, [], [77485]⟩
      ]⟩,
    ⟨[507], [508], .contexts [
        ⟨2708, true, true, [], []⟩
      ]⟩,
    ⟨[77485, 9], [507, 77471], .contexts [
        ⟨2710, true, false, [508], [9]⟩,
        ⟨76, false, false, [508, 77471], []⟩,
        ⟨2711, true, false, [], [77471]⟩
      ]⟩,
    ⟨[509, 77485], [509, 77485], .contexts []⟩,
    ⟨[77471, 9], [509, 77485], .contexts [
        ⟨2707, false, false, [], []⟩,
        ⟨2710, false, false, [], []⟩,
        ⟨2713, false, false, [], []⟩,
        ⟨2713, false, false, [], []⟩
      ]⟩,
    ⟨[511], [509, 257], .source 320⟩,
    ⟨[513], [511, 507], .source 321⟩,
    ⟨[515], [513, 439], .source 322⟩,
    ⟨[77467, 9], [77467, 9], .contexts []⟩,
    ⟨[517], [514], .source 323⟩,
    ⟨[519], [517, 439], .source 324⟩,
    ⟨[77467, 9], [519, 77467], .contexts [
        ⟨2718, false, false, [], []⟩,
        ⟨2717, false, false, [514], [77467, 9]⟩,
        ⟨2503, true, false, [514, 513], [9]⟩,
        ⟨2286, true, false, [514, 513], [9]⟩,
        ⟨2716, false, false, [514], [77471, 1, 9]⟩,
        ⟨2712, true, false, [514, 511], [1, 9]⟩,
        ⟨2715, false, false, [514], [77485, 9, 1, 9]⟩,
        ⟨2685, true, false, [514, 509], [9, 1, 9]⟩,
        ⟨2714, true, false, [514], [1, 9, 1, 9]⟩,
        ⟨885, false, false, [514, 77471], []⟩,
        ⟨2480, false, false, [514], []⟩,
        ⟨2510, false, false, [514], []⟩,
        ⟨2489, false, false, [514, 439], []⟩,
        ⟨2719, true, false, [], [439, 77467]⟩,
        ⟨2720, true, false, [], [77467]⟩
      ]⟩,
    ⟨[519, 77467], [519, 77467], .contexts []⟩,
    ⟨[77465, 9], [77465, 9], .contexts []⟩,
    ⟨[521], [518], .source 325⟩,
    ⟨[518], [518], .contexts []⟩,
    ⟨[521, 77465], [521, 77465], .contexts []⟩,
    ⟨[77465, 9], [521, 77465], .contexts [
        ⟨2723, false, false, [], []⟩,
        ⟨2723, false, false, [], []⟩,
        ⟨2279, true, false, [], [9]⟩,
        ⟨2722, true, false, [518], [13, 9]⟩,
        ⟨2722, true, false, [518], [13, 9]⟩,
        ⟨2721, true, false, [518], [13, 9]⟩,
        ⟨2718, true, false, [518], [13, 9]⟩,
        ⟨926, false, false, [518, 77467], []⟩,
        ⟨2516, false, false, [518], []⟩,
        ⟨2515, false, false, [518], []⟩,
        ⟨2518, false, false, [518], []⟩,
        ⟨2725, true, false, [], [77465]⟩,
        ⟨2725, true, false, [], [77465]⟩,
        ⟨2724, true, false, [], [77465]⟩,
        ⟨2726, false, false, [], []⟩,
        ⟨2726, false, false, [], []⟩
      ]⟩,
    ⟨[523], [521, 461], .source 326⟩,
    ⟨[525], [523, 471], .source 327⟩,
    ⟨[77463], [461, 77461], .contexts [
        ⟨2547, false, false, [], []⟩
      ]⟩,
    ⟨[77455, 9], [524, 461, 77461], .contexts [
        ⟨2729, false, false, [524], [77455, 9]⟩,
        ⟨2561, true, false, [524, 523], [9]⟩,
        ⟨2556, false, false, [524, 523], [77455, 9]⟩,
        ⟨2560, true, false, [524, 523], [9]⟩,
        ⟨2555, false, false, [524, 523], [77455, 9]⟩,
        ⟨18, true, false, [524, 523, 468, 77455], [9]⟩,
        ⟨2564, false, false, [524, 523, 468], [1, 9]⟩,
        ⟨2312, false, false, [524, 523], [9]⟩,
        ⟨2313, false, false, [524, 523], [9]⟩,
        ⟨2265, false, false, [524, 523], [9]⟩,
        ⟨2265, false, false, [524, 523], [9]⟩,
        ⟨2266, true, false, [524, 523], [9]⟩,
        ⟨2269, true, false, [524, 523], [1, 9]⟩,
        ⟨2728, false, false, [524], [77461, 9, 1, 9]⟩,
        ⟨2547, true, false, [524, 521], [9, 1, 9]⟩,
        ⟨2275, true, false, [524, 521], [9, 1, 9]⟩,
        ⟨2727, true, false, [524], [1, 9, 1, 9]⟩,
        ⟨885, false, false, [524, 77465], []⟩,
        ⟨2538, false, false, [524], []⟩,
        ⟨2536, false, false, [524], []⟩,
        ⟨2730, false, false, [524], []⟩,
        ⟨2542, false, false, [524], []⟩,
        ⟨2542, false, false, [524], []⟩
      ]⟩,
    ⟨[77461], [77461], .contexts []⟩,
    ⟨[527], [524], .source 328⟩,
    ⟨[529], [527, 461], .source 329⟩,
    ⟨[77455, 9], [529, 77461], .contexts [
        ⟨2731, false, false, [], []⟩,
        ⟨2732, false, false, [524, 461], []⟩,
        ⟨2733, true, false, [], [461, 77461]⟩,
        ⟨2734, true, false, [], [77461]⟩
      ]⟩,
    ⟨[531], [528], .source 330⟩,
    ⟨[77459], [531, 77455], .contexts [
        ⟨2552, true, false, [], []⟩,
        ⟨2735, true, false, [528], [9]⟩,
        ⟨76, false, false, [528, 77455], []⟩,
        ⟨2736, true, false, [], [77455]⟩
      ]⟩,
    ⟨[77455, 3], [77453], .contexts [
        ⟨2314, false, false, [], []⟩,
        ⟨2315, false, false, [], []⟩,
        ⟨2259, false, false, [], []⟩,
        ⟨2259, false, false, [], []⟩
      ]⟩,
    ⟨[533], [469, 531], .source 331⟩,
    ⟨[533, 77451], [533, 77451], .contexts []⟩,
    ⟨[533, 77451], [533, 77451], .contexts []⟩,
    ⟨[3, 1, 3], [0, 2, 0], .contexts [
        ⟨212, false, false, [], [0, 2, 0]⟩
      ]⟩,
    ⟨[77451, 3], [77451, 3], .contexts []⟩,
    ⟨[77451], [77451], .contexts []⟩,
    ⟨[77451, 3], [533, 77451], .contexts [
        ⟨2743, false, false, [], []⟩,
        ⟨2743, false, false, [], []⟩,
        ⟨2255, true, false, [], [3]⟩,
        ⟨2255, true, false, [], [3]⟩,
        ⟨2318, true, false, [], [3]⟩,
        ⟨2317, true, false, [], [3]⟩,
        ⟨2738, true, false, [], [1, 3]⟩,
        ⟨2742, false, false, [77455], []⟩,
        ⟨215, false, false, [77455], []⟩,
        ⟨2562, false, false, [], [3, 1]⟩,
        ⟨2564, false, false, [], [3, 1]⟩,
        ⟨2737, false, false, [469], [3, 1]⟩,
        ⟨2739, true, false, [], [77455, 3, 1]⟩,
        ⟨2260, false, false, [533], [1]⟩,
        ⟨2256, false, false, [533], []⟩,
        ⟨2740, false, false, [], []⟩,
        ⟨2741, false, false, [], []⟩,
        ⟨2744, false, false, [533], []⟩,
        ⟨24, true, false, [], [533, 77451]⟩,
        ⟨2740, false, false, [], []⟩,
        ⟨2741, false, false, [], []⟩
      ]⟩,
    ⟨[77451, 15], [77449], .contexts [
        ⟨2319, false, false, [], []⟩,
        ⟨2320, false, false, [], []⟩,
        ⟨2251, false, false, [], []⟩,
        ⟨2251, false, false, [], []⟩
      ]⟩,
    ⟨[77449, 3], [77449, 3], .contexts []⟩,
    ⟨[77449], [77449], .contexts []⟩,
    ⟨[535], [532], .source 332⟩,
    ⟨[532], [532], .contexts []⟩,
    ⟨[535, 77449], [535, 77449], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 043. -/
def y322TCContextRaw043 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77447], [77447], .contexts []⟩,
    ⟨[77487], [77485, 13], .source 38808⟩,
    ⟨[77485, 13], [77487], .contexts [
        ⟨2753, true, false, [], []⟩
      ]⟩,
    ⟨[77487, 13], [77485], .contexts [
        ⟨2754, true, false, [], [13]⟩,
        ⟨98, false, false, [77485], []⟩,
        ⟨2678, false, false, [], []⟩
      ]⟩,
    ⟨[77487], [77487], .contexts []⟩,
    ⟨[77487], [77487], .contexts []⟩,
    ⟨[77485, 13], [77487], .contexts [
        ⟨2754, false, false, [], []⟩,
        ⟨2756, false, false, [], []⟩,
        ⟨2757, false, false, [], []⟩,
        ⟨2757, false, false, [], []⟩
      ]⟩,
    ⟨[503, 77115], [503, 77115], .contexts []⟩,
    ⟨[503, 77115], [503, 77115], .contexts []⟩,
    ⟨[77487, 3], [77487, 3], .contexts []⟩,
    ⟨[77487, 3], [503, 77115], .contexts [
        ⟨2761, false, false, [], []⟩,
        ⟨2758, true, false, [], [3]⟩,
        ⟨107, false, false, [77485], []⟩,
        ⟨109, false, false, [77485], []⟩,
        ⟨2704, false, false, [], [13]⟩,
        ⟨374, false, false, [503], []⟩,
        ⟨2759, false, false, [], []⟩,
        ⟨2760, false, false, [], []⟩,
        ⟨392, false, false, [503], []⟩,
        ⟨2689, true, false, [], [77115]⟩
      ]⟩,
    ⟨[77487], [77487], .contexts []⟩,
    ⟨[77487, 5], [261, 77487], .contexts [
        ⟨2758, true, false, [], [5]⟩,
        ⟨116, false, false, [77485], []⟩,
        ⟨117, false, false, [77485], []⟩,
        ⟨2695, false, false, [], [13]⟩,
        ⟨2697, false, false, [], [13]⟩,
        ⟨2693, false, false, [], [13]⟩,
        ⟨2694, false, false, [], [13]⟩,
        ⟨2694, false, false, [], [13]⟩,
        ⟨2754, false, false, [261], []⟩,
        ⟨2763, false, false, [261], []⟩,
        ⟨2696, true, false, [], [77487]⟩
      ]⟩,
    ⟨[77487, 11], [77487, 11], .contexts []⟩,
    ⟨[77487, 11], [77347], .contexts [
        ⟨2765, false, false, [], []⟩,
        ⟨2758, true, false, [], [11]⟩,
        ⟨137, false, false, [77485], []⟩,
        ⟨138, false, false, [77485], []⟩,
        ⟨2676, false, false, [], [13]⟩,
        ⟨1361, false, false, [], [13]⟩,
        ⟨1349, false, false, [], [13]⟩,
        ⟨1349, false, false, [], [13]⟩,
        ⟨1362, false, false, [], []⟩,
        ⟨1363, false, false, [], []⟩,
        ⟨1345, false, false, [], []⟩,
        ⟨1345, false, false, [], []⟩,
        ⟨1581, false, false, [], []⟩,
        ⟨1118, true, false, [], [77347]⟩
      ]⟩,
    ⟨[3, 15, 3, 15], [], .contexts [
        ⟨244, false, false, [], []⟩
      ]⟩,
    ⟨[77487], [77487], .contexts []⟩,
    ⟨[77119, 15], [77119, 15], .contexts []⟩,
    ⟨[502], [502], .contexts []⟩,
    ⟨[505], [502], .contexts [
        ⟨2691, false, false, [], []⟩,
        ⟨2770, false, false, [], []⟩,
        ⟨2770, false, false, [], []⟩
      ]⟩,
    ⟨[77119, 15], [505, 77487], .contexts [
        ⟨2769, false, false, [], []⟩,
        ⟨415, true, false, [], [15]⟩,
        ⟨395, true, false, [], [3, 15]⟩,
        ⟨2760, true, false, [502], [15, 3, 15]⟩,
        ⟨2760, true, false, [502], [15, 3, 15]⟩,
        ⟨2759, true, false, [502], [15, 3, 15]⟩,
        ⟨2762, true, false, [502], [15, 3, 15]⟩,
        ⟨2761, true, false, [502], [15, 3, 15]⟩,
        ⟨2767, false, false, [502, 77487], []⟩,
        ⟨2768, false, false, [502], []⟩,
        ⟨2763, false, false, [502], []⟩,
        ⟨2771, true, false, [], [77487]⟩
      ]⟩,
    ⟨[503], [504], .contexts [
        ⟨2691, true, true, [], []⟩
      ]⟩,
    ⟨[77343, 1], [77487], .contexts [
        ⟨1337, true, false, [], [1]⟩,
        ⟨1337, true, false, [], [1]⟩,
        ⟨1367, true, false, [], [1]⟩,
        ⟨1366, true, false, [], [1]⟩,
        ⟨1341, true, false, [], [11, 1]⟩,
        ⟨1341, true, false, [], [11, 1]⟩,
        ⟨1365, true, false, [], [11, 1]⟩,
        ⟨1364, true, false, [], [11, 1]⟩,
        ⟨1345, true, false, [], [1, 11, 1]⟩,
        ⟨1345, true, false, [], [1, 11, 1]⟩,
        ⟨1363, true, false, [], [1, 11, 1]⟩,
        ⟨2766, true, false, [], [1, 11, 1]⟩,
        ⟨2765, true, false, [], [1, 11, 1]⟩,
        ⟨1068, false, false, [77487], []⟩,
        ⟨2768, false, false, [], []⟩,
        ⟨2763, false, false, [], []⟩,
        ⟨1118, true, false, [], [77487]⟩
      ]⟩,
    ⟨[77487, 1], [77343], .contexts [
        ⟨2774, true, false, [], [1]⟩,
        ⟨18, false, false, [77343], []⟩,
        ⟨1337, false, false, [], []⟩
      ]⟩,
    ⟨[505, 77487], [505, 77487], .contexts []⟩,
    ⟨[77119, 15], [505, 77487], .contexts [
        ⟨2769, false, false, [], []⟩,
        ⟨2772, false, false, [], []⟩,
        ⟨2776, false, false, [], []⟩,
        ⟨2776, false, false, [], []⟩
      ]⟩,
    ⟨[15, 1, 15], [0], .contexts [
        ⟨16, false, false, [], [0]⟩
      ]⟩,
    ⟨[77343, 15], [77343, 15], .contexts []⟩,
    ⟨[537], [503, 317], .source 333⟩,
    ⟨[77343, 15], [537, 77123], .contexts [
        ⟨2779, false, false, [], []⟩,
        ⟨2775, true, false, [], [15]⟩,
        ⟨2777, true, false, [504], [1, 15]⟩,
        ⟨2778, false, false, [504, 77119], []⟩,
        ⟨1952, false, false, [504], []⟩,
        ⟨1950, false, false, [504], []⟩,
        ⟨1954, false, false, [504, 317], []⟩,
        ⟨2773, true, false, [], [317, 77123]⟩,
        ⟨2780, true, false, [], [77123]⟩
      ]⟩,
    ⟨[539], [536], .source 334⟩,
    ⟨[77123, 15], [539, 77343], .contexts [
        ⟨2781, true, false, [536], [15]⟩,
        ⟨3, false, false, [536, 77343], []⟩,
        ⟨2782, true, false, [], [77343]⟩
      ]⟩,
    ⟨[537, 77123], [537, 77123], .contexts []⟩,
    ⟨[537, 77125], [537, 77125], .contexts []⟩,
    ⟨[537, 77125], [537, 77125], .contexts []⟩,
    ⟨[15, 9, 15], [8], .contexts [
        ⟨74, false, false, [], [8]⟩
      ]⟩,
    ⟨[77125, 15], [77125, 15], .contexts []⟩,
    ⟨[539], [536], .contexts [
        ⟨2782, false, false, [], []⟩
      ]⟩,
    ⟨[536], [536], .contexts []⟩,
    ⟨[77125, 15], [539, 77341], .contexts [
        ⟨2788, false, false, [], []⟩,
        ⟨2786, true, false, [536], [15]⟩,
        ⟨2785, true, false, [536], [15]⟩,
        ⟨431, true, false, [], [15]⟩,
        ⟨2784, true, false, [536], [9, 15]⟩,
        ⟨2784, true, false, [536], [9, 15]⟩,
        ⟨2781, true, false, [536], [9, 15]⟩,
        ⟨2779, true, false, [536], [9, 15]⟩,
        ⟨2787, false, false, [536, 77343], []⟩,
        ⟨1651, false, false, [536], []⟩,
        ⟨1649, false, false, [536], []⟩,
        ⟨1653, false, false, [536], []⟩,
        ⟨2790, true, false, [], [77341]⟩,
        ⟨2790, true, false, [], [77341]⟩,
        ⟨2789, true, false, [], [77341]⟩
      ]⟩,
    ⟨[537], [538], .contexts [
        ⟨2782, true, true, [], []⟩
      ]⟩,
    ⟨[77341, 15], [537, 77125], .contexts [
        ⟨2791, true, false, [538], [15]⟩,
        ⟨3, false, false, [538, 77125], []⟩,
        ⟨2792, true, false, [], [77125]⟩
      ]⟩,
    ⟨[77489], [77119, 9], .source 38809⟩,
    ⟨[77119, 9], [77489], .contexts [
        ⟨2794, true, false, [], []⟩
      ]⟩,
    ⟨[77489, 9], [77119], .contexts [
        ⟨2795, true, false, [], [9]⟩,
        ⟨76, false, false, [77119], []⟩,
        ⟨417, false, false, [], []⟩
      ]⟩,
    ⟨[77489], [77489], .contexts []⟩,
    ⟨[77489], [77489], .contexts []⟩,
    ⟨[77119, 9], [77489], .contexts [
        ⟨2795, false, false, [], []⟩,
        ⟨2797, false, false, [], []⟩,
        ⟨2798, false, false, [], []⟩,
        ⟨2798, false, false, [], []⟩
      ]⟩,
    ⟨[77117, 9], [245, 77243], .contexts [
        ⟨1641, false, false, [], []⟩
      ]⟩,
    ⟨[77489, 3], [77489, 3], .contexts []⟩,
    ⟨[245, 77243], [245, 77243], .contexts [
        ⟨1181, false, false, [245], []⟩
      ]⟩,
    ⟨[245, 77243], [245, 77243], .contexts [
        ⟨1606, true, false, [], [77243]⟩
      ]⟩,
    ⟨[77489, 3], [245, 77243], .contexts [
        ⟨2801, false, false, [], []⟩,
        ⟨2799, true, false, [], [3]⟩,
        ⟨306, false, false, [77119], []⟩,
        ⟨307, false, false, [77119], []⟩,
        ⟨1946, false, false, [], [9]⟩,
        ⟨2800, false, false, [], []⟩,
        ⟨1633, false, false, [], []⟩,
        ⟨1635, false, false, [], []⟩,
        ⟨1635, false, false, [], []⟩,
        ⟨2802, false, false, [], []⟩,
        ⟨2803, false, false, [], []⟩
      ]⟩,
    ⟨[77243, 3], [243, 77489], .contexts [
        ⟨2804, true, false, [244], [3]⟩,
        ⟨35, false, false, [244, 77489], []⟩,
        ⟨1544, true, false, [], [77489]⟩
      ]⟩,
    ⟨[315, 77119, 9], [315, 77489], .contexts [
        ⟨2795, false, false, [315], []⟩
      ]⟩,
    ⟨[315, 77489], [315, 77489], .contexts []⟩,
    ⟨[315, 77489], [315, 77489], .contexts []⟩,
    ⟨[315, 77489], [315, 77489], .contexts []⟩,
    ⟨[77489, 5], [77489, 5], .contexts []⟩,
    ⟨[77489], [77489], .contexts []⟩,
    ⟨[315], [315], .contexts [
        ⟨24, false, false, [], [315]⟩
      ]⟩,
    ⟨[13, 77489], [13, 77489], .contexts []⟩,
    ⟨[13, 77489], [13, 77489], .contexts []⟩,
    ⟨[13, 77489], [13, 77489], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 044. -/
def y322TCContextRaw044 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77489, 13], [13, 77489], .contexts [
        ⟨2799, true, false, [], [13]⟩,
        ⟨315, false, false, [77119], []⟩,
        ⟨316, false, false, [77119], []⟩,
        ⟨426, false, false, [], [9]⟩,
        ⟨2795, false, false, [13], []⟩,
        ⟨2813, false, false, [], []⟩,
        ⟨2814, false, false, [], []⟩,
        ⟨2815, false, false, [], []⟩,
        ⟨2811, false, false, [13], []⟩,
        ⟨153, true, false, [], [77489]⟩
      ]⟩,
    ⟨[77489, 3], [245, 77243], .contexts [
        ⟨2801, false, false, [], []⟩,
        ⟨2804, false, false, [], []⟩,
        ⟨1633, false, false, [], []⟩,
        ⟨1635, false, false, [], []⟩,
        ⟨1635, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77243, 11], [245, 243, 77243], .contexts [
        ⟨1643, false, false, [245], []⟩
      ]⟩,
    ⟨[245, 243, 77243], [245, 243, 77243], .contexts []⟩,
    ⟨[245, 243, 77243], [245, 243, 77243], .contexts []⟩,
    ⟨[245, 243, 77243], [77243], .contexts [
        ⟨1540, false, false, [], [243, 77243]⟩
      ]⟩,
    ⟨[243, 77489], [243, 77489], .contexts []⟩,
    ⟨[3, 11, 3, 11], [], .contexts [
        ⟨230, false, false, [], []⟩
      ]⟩,
    ⟨[77489, 11], [77489, 11], .contexts []⟩,
    ⟨[77489, 11], [245, 77489], .contexts [
        ⟨2824, false, false, [], []⟩,
        ⟨2822, true, false, [242], [11]⟩,
        ⟨2822, true, false, [242], [11]⟩,
        ⟨2805, true, false, [242], [11]⟩,
        ⟨2821, true, false, [242], [3, 11]⟩,
        ⟨2820, true, false, [242], [3, 11]⟩,
        ⟨2819, true, false, [242], [3, 11]⟩,
        ⟨2818, true, false, [242], [3, 11]⟩,
        ⟨2817, true, false, [242], [11, 3, 11]⟩,
        ⟨2823, false, false, [242, 77489], []⟩,
        ⟨2811, false, false, [242], []⟩,
        ⟨1670, true, false, [], [77489]⟩
      ]⟩,
    ⟨[77491], [77489, 1], .source 38810⟩,
    ⟨[77489, 1], [77491], .contexts [
        ⟨2826, true, false, [], []⟩
      ]⟩,
    ⟨[77491, 1], [77489], .contexts [
        ⟨2827, true, false, [], [1]⟩,
        ⟨18, false, false, [77489], []⟩,
        ⟨2798, false, false, [], []⟩
      ]⟩,
    ⟨[77491], [77491], .contexts []⟩,
    ⟨[77489, 1], [77491], .contexts [
        ⟨2827, false, false, [], []⟩,
        ⟨2829, false, false, [], []⟩,
        ⟨2829, false, false, [], []⟩
      ]⟩,
    ⟨[541], [245, 295], .source 335⟩,
    ⟨[77491, 3], [77491, 3], .contexts []⟩,
    ⟨[541], [541], .contexts [
        ⟨24, false, false, [], [541]⟩
      ]⟩,
    ⟨[77491, 3], [541, 77203], .contexts [
        ⟨2832, false, false, [], []⟩,
        ⟨2830, true, false, [], [3]⟩,
        ⟨1824, false, false, [77489], []⟩,
        ⟨1826, false, false, [77489], []⟩,
        ⟨2817, false, false, [], [1, 3, 1]⟩,
        ⟨1183, false, false, [245], [3, 1]⟩,
        ⟨1688, false, false, [], [3, 1]⟩,
        ⟨1689, false, false, [], [3, 1]⟩,
        ⟨1691, false, false, [], [1]⟩,
        ⟨1692, false, false, [], [1]⟩,
        ⟨1693, false, false, [], [1]⟩,
        ⟨1694, false, false, [], [1]⟩,
        ⟨1902, false, false, [245], []⟩,
        ⟨2831, true, false, [], [77203]⟩,
        ⟨1056, false, false, [541], []⟩,
        ⟨2833, true, false, [], [77203]⟩
      ]⟩,
    ⟨[543], [540], .source 336⟩,
    ⟨[315, 77489, 1], [315, 77491], .contexts [
        ⟨2827, false, false, [315], []⟩
      ]⟩,
    ⟨[315, 77491], [315, 77491], .contexts []⟩,
    ⟨[315, 77491], [315, 77491], .contexts []⟩,
    ⟨[315, 77491], [315, 77491], .contexts []⟩,
    ⟨[77491, 5], [77491, 5], .contexts []⟩,
    ⟨[77491, 5], [315, 77491], .contexts [
        ⟨2840, false, false, [], []⟩,
        ⟨2830, true, false, [], [5]⟩,
        ⟨165, false, false, [77489], []⟩,
        ⟨166, false, false, [77489], []⟩,
        ⟨2810, false, false, [], [1]⟩,
        ⟨2810, false, false, [], [1]⟩,
        ⟨2799, true, false, [], [5, 1]⟩,
        ⟨1805, false, false, [77119], [1]⟩,
        ⟨1806, false, false, [77119], [1]⟩,
        ⟨1959, false, false, [], [9, 1]⟩,
        ⟨2806, false, false, [], [1]⟩,
        ⟨2807, false, false, [], [1]⟩,
        ⟨2808, false, false, [], [1]⟩,
        ⟨2809, false, false, [], [1]⟩,
        ⟨2811, false, false, [315], [1]⟩,
        ⟨2812, true, false, [], [77489, 1]⟩,
        ⟨2807, false, false, [], [1]⟩,
        ⟨2809, false, false, [], [1]⟩,
        ⟨2809, false, false, [], [1]⟩,
        ⟨2836, false, false, [], []⟩,
        ⟨2837, false, false, [], []⟩,
        ⟨2838, false, false, [], []⟩,
        ⟨2839, false, false, [], []⟩
      ]⟩,
    ⟨[77491], [77491], .contexts []⟩,
    ⟨[315, 77491], [315, 77491], .contexts [
        ⟨2842, false, false, [315], []⟩
      ]⟩,
    ⟨[315, 77491], [315, 77491], .contexts [
        ⟨2812, true, false, [], [77491]⟩
      ]⟩,
    ⟨[77491, 5], [315, 77491], .contexts [
        ⟨2841, false, false, [], []⟩,
        ⟨2843, false, false, [], []⟩,
        ⟨2844, false, false, [], []⟩
      ]⟩,
    ⟨[77489, 11], [245, 77489], .contexts [
        ⟨2825, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77489], [245, 77489], .contexts []⟩,
    ⟨[245, 77489], [245, 77489], .contexts []⟩,
    ⟨[245, 77491], [245, 77491], .contexts []⟩,
    ⟨[245, 77491], [245, 77491], .contexts []⟩,
    ⟨[77491, 11], [77491, 11], .contexts []⟩,
    ⟨[77491, 11], [245, 77491], .contexts [
        ⟨2851, false, false, [], []⟩,
        ⟨2830, true, false, [], [11]⟩,
        ⟨181, false, false, [77489], []⟩,
        ⟨182, false, false, [77489], []⟩,
        ⟨2824, false, false, [], [1]⟩,
        ⟨2846, false, false, [], [1]⟩,
        ⟨2847, false, false, [], [1]⟩,
        ⟨2848, false, false, [], [1]⟩,
        ⟨2848, false, false, [], [1]⟩,
        ⟨2827, false, false, [245], []⟩,
        ⟨2849, false, false, [], []⟩,
        ⟨2850, false, false, [], []⟩,
        ⟨2842, false, false, [245], []⟩,
        ⟨1606, true, false, [], [77491]⟩
      ]⟩,
    ⟨[541, 77203], [541, 77203], .contexts []⟩,
    ⟨[77491, 3], [541, 77203], .contexts [
        ⟨2832, false, false, [], []⟩,
        ⟨2834, false, false, [], []⟩,
        ⟨2853, false, false, [], []⟩,
        ⟨2853, false, false, [], []⟩
      ]⟩,
    ⟨[545], [541, 293], .source 337⟩,
    ⟨[77491, 5], [315, 77491], .contexts [
        ⟨2840, false, false, [], []⟩,
        ⟨2845, false, false, [], []⟩,
        ⟨2837, false, false, [], []⟩,
        ⟨2839, false, false, [], []⟩,
        ⟨2839, false, false, [], []⟩
      ]⟩,
    ⟨[315, 77491, 3], [315, 541, 77203], .contexts [
        ⟨2834, false, false, [315], []⟩
      ]⟩,
    ⟨[315, 541, 77203], [315, 541, 77203], .contexts []⟩,
    ⟨[315, 541, 77203], [315, 541, 77203], .contexts []⟩,
    ⟨[547], [315, 541], .source 338⟩,
    ⟨[315, 541, 77203], [547, 77203], .contexts [
        ⟨2860, true, false, [], [77203]⟩
      ]⟩,
    ⟨[549], [547, 293], .source 339⟩,
    ⟨[3, 5, 3], [4, 2, 4], .contexts [
        ⟨1478, false, false, [], [4, 2, 4]⟩
      ]⟩,
    ⟨[77251, 3], [77251, 3], .contexts []⟩,
    ⟨[551], [544], .source 340⟩,
    ⟨[553], [551, 549], .source 341⟩,
    ⟨[77251, 3], [553, 77251], .contexts [
        ⟨2864, false, false, [], []⟩,
        ⟨2855, false, false, [544], [77251, 3]⟩,
        ⟨1911, true, false, [544, 541], [3]⟩,
        ⟨2854, true, false, [544], [5, 3]⟩,
        ⟨2863, false, false, [544, 77491], []⟩,
        ⟨1480, false, false, [544, 77491], []⟩,
        ⟨2856, false, false, [544], [3, 5]⟩,
        ⟨2857, false, false, [544], [5]⟩,
        ⟨2858, false, false, [544], [5]⟩,
        ⟨2859, false, false, [544], [5]⟩,
        ⟨2861, false, false, [544], [5]⟩,
        ⟨1911, false, false, [544, 547], []⟩,
        ⟨2862, true, false, [544], [77251]⟩,
        ⟨1724, false, false, [544, 549], []⟩,
        ⟨2865, true, false, [], [549, 77251]⟩,
        ⟨2866, true, false, [], [77251]⟩
      ]⟩,
    ⟨[553, 77251], [553, 77251], .contexts []⟩,
    ⟨[77253, 3], [77253, 3], .contexts []⟩,
    ⟨[555], [552], .source 342⟩,
    ⟨[552], [552], .contexts []⟩,
    ⟨[555, 77253], [555, 77253], .contexts []⟩,
    ⟨[555, 77253], [555, 77253], .contexts []⟩,
    ⟨[77253, 3], [555, 77253], .contexts [
        ⟨2869, false, false, [], []⟩,
        ⟨2869, false, false, [], []⟩,
        ⟨1195, true, false, [], [3]⟩,
        ⟨2868, true, false, [552], [9, 3]⟩,
        ⟨2868, true, false, [552], [9, 3]⟩,
        ⟨2867, true, false, [552], [9, 3]⟩,
        ⟨2864, true, false, [552], [9, 3]⟩,
        ⟨1010, false, false, [552, 77251], []⟩,
        ⟨77, false, false, [552, 77251], []⟩,
        ⟨1737, false, false, [552], []⟩,
        ⟨1719, false, false, [552], []⟩,
        ⟨2871, true, false, [], [77253]⟩,
        ⟨2871, true, false, [], [77253]⟩,
        ⟨2870, true, false, [], [77253]⟩,
        ⟨2872, false, false, [], []⟩,
        ⟨2873, false, false, [], []⟩,
        ⟨2873, false, false, [], []⟩
      ]⟩,
    ⟨[77255, 3], [77255, 3], .contexts []⟩,
    ⟨[554], [554], .contexts []⟩,
    ⟨[553, 77255], [553, 77255], .contexts []⟩,
    ⟨[557], [553, 275], .source 343⟩,
    ⟨[77255, 3, 13], [557, 77259], .contexts [
        ⟨2875, false, false, [], [13]⟩,
        ⟨2875, false, false, [], [13]⟩,
        ⟨1198, true, false, [], [3, 13]⟩,
        ⟨2874, true, false, [554], [11, 3, 13]⟩,
        ⟨976, false, false, [554, 77253], [13]⟩,
        ⟨91, false, false, [554, 77253], [13]⟩,
        ⟨1731, false, false, [554], [13]⟩,
        ⟨1740, false, false, [554], [13]⟩,
        ⟨2876, true, false, [], [77255, 13]⟩,
        ⟨2876, true, false, [], [77255, 13]⟩,
        ⟨2870, false, true, [], [77255, 13]⟩,
        ⟨2877, false, false, [], [13]⟩,
        ⟨2877, false, false, [], [13]⟩,
        ⟨1735, false, false, [553], []⟩,
        ⟨2878, true, false, [], [77259]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 045. -/
def y322TCContextRaw045 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77259, 3], [77259, 3], .contexts []⟩,
    ⟨[559], [556], .source 344⟩,
    ⟨[561], [559, 275], .source 345⟩,
    ⟨[561, 77259], [561, 77259], .contexts []⟩,
    ⟨[561, 77261, 3], [77259, 15], .contexts [
        ⟨1207, true, false, [561], [3]⟩,
        ⟨2883, true, false, [], [15, 3]⟩,
        ⟨2883, true, false, [], [15, 3]⟩,
        ⟨2882, false, false, [], [77259, 15, 3]⟩,
        ⟨2881, false, false, [], [275, 77259, 15, 3]⟩,
        ⟨1749, true, false, [556, 275], [15, 3]⟩,
        ⟨1745, true, false, [556], [15, 3]⟩,
        ⟨108, true, false, [556, 77255], [15, 3]⟩,
        ⟨932, true, false, [556, 77255], [15, 3]⟩,
        ⟨2879, false, false, [556], [3, 15, 3]⟩,
        ⟨2880, true, false, [], [15, 3]⟩,
        ⟨2880, true, false, [], [15, 3]⟩,
        ⟨900, false, false, [77259], []⟩,
        ⟨1754, false, false, [], []⟩
      ]⟩,
    ⟨[77261, 3], [77261, 3], .contexts []⟩,
    ⟨[563], [560], .source 346⟩,
    ⟨[560], [560], .contexts []⟩,
    ⟨[563], [560], .contexts [
        ⟨2886, false, false, [], []⟩,
        ⟨2887, false, false, [], []⟩,
        ⟨2887, false, false, [], []⟩
      ]⟩,
    ⟨[563, 77261], [563, 77261], .contexts []⟩,
    ⟨[77263, 3], [77265], .contexts [
        ⟨1215, false, false, [], []⟩
      ]⟩,
    ⟨[3, 1, 3, 1], [0, 2], .contexts [
        ⟨212, false, false, [], [0, 2]⟩
      ]⟩,
    ⟨[563, 77265, 1], [77261, 1, 3], .contexts [
        ⟨1215, true, false, [563], [1]⟩,
        ⟨1211, true, false, [563], [3, 1]⟩,
        ⟨2889, true, false, [], [1, 3, 1]⟩,
        ⟨2889, true, false, [], [1, 3, 1]⟩,
        ⟨2888, false, false, [], [77261, 1, 3, 1]⟩,
        ⟨1755, true, false, [560], [1, 3, 1]⟩,
        ⟨1753, true, false, [560], [1, 3, 1]⟩,
        ⟨2884, true, false, [560], [1, 3, 1]⟩,
        ⟨2885, true, false, [], [1, 3, 1]⟩,
        ⟨2885, true, false, [], [1, 3, 1]⟩,
        ⟨2891, false, false, [77261], []⟩,
        ⟨214, false, false, [77261], []⟩
      ]⟩,
    ⟨[77265, 1], [77265, 1], .contexts []⟩,
    ⟨[77265], [77265], .contexts []⟩,
    ⟨[561], [562], .contexts [
        ⟨2886, true, true, [], []⟩
      ]⟩,
    ⟨[561], [561], .contexts []⟩,
    ⟨[561], [562], .contexts [
        ⟨2895, false, false, [], []⟩
      ]⟩,
    ⟨[562], [562], .contexts []⟩,
    ⟨[77265, 1], [561, 77265], .contexts [
        ⟨2893, false, false, [], []⟩,
        ⟨2892, false, false, [562], []⟩,
        ⟨1211, false, false, [562], [3]⟩,
        ⟨1414, false, false, [562], [3]⟩,
        ⟨1216, false, false, [562], [3]⟩,
        ⟨1216, false, false, [562], [3]⟩,
        ⟨2890, false, false, [562], []⟩,
        ⟨1412, false, false, [562], []⟩,
        ⟨1219, false, false, [562], []⟩,
        ⟨1219, false, false, [562], []⟩,
        ⟨2894, false, false, [562], []⟩,
        ⟨2898, true, false, [], [77265]⟩,
        ⟨2898, true, false, [], [77265]⟩,
        ⟨2897, true, false, [], [77265]⟩,
        ⟨2896, true, false, [], [77265]⟩
      ]⟩,
    ⟨[561, 77265], [561, 77265], .contexts []⟩,
    ⟨[561, 77269], [561, 77269], .contexts []⟩,
    ⟨[77269, 5], [563, 77265], .contexts [
        ⟨2901, true, false, [560], [5]⟩,
        ⟨1222, true, false, [], [5]⟩,
        ⟨1218, true, false, [], [1, 5]⟩,
        ⟨2900, true, false, [560], [5, 1, 5]⟩,
        ⟨2900, true, false, [560], [5, 1, 5]⟩,
        ⟨2899, true, false, [560], [5, 1, 5]⟩,
        ⟨2893, true, false, [560], [5, 1, 5]⟩,
        ⟨1909, false, false, [560, 77265], []⟩,
        ⟨2894, false, false, [560], []⟩,
        ⟨2888, true, false, [], [77265]⟩
      ]⟩,
    ⟨[77265, 5], [77267], .contexts [
        ⟨1218, false, false, [], []⟩
      ]⟩,
    ⟨[77269], [563, 77267], .contexts [
        ⟨2896, false, false, [560], [77269]⟩,
        ⟨2901, true, false, [560], []⟩,
        ⟨2895, false, false, [560], [77269]⟩,
        ⟨49, true, false, [560, 562, 77269], []⟩,
        ⟨2902, false, false, [560, 562], [5]⟩,
        ⟨2903, false, false, [560], []⟩,
        ⟨1410, false, false, [560], []⟩,
        ⟨1223, false, false, [560], []⟩,
        ⟨1223, false, false, [560], []⟩,
        ⟨2886, true, false, [], [77267]⟩
      ]⟩,
    ⟨[77267, 9], [561, 77271], .contexts [
        ⟨2904, true, false, [562], [9]⟩,
        ⟨1225, false, false, [562], []⟩,
        ⟨1407, false, false, [562], []⟩,
        ⟨2898, true, false, [], [77271]⟩,
        ⟨2898, true, false, [], [77271]⟩,
        ⟨2897, true, false, [], [77271]⟩
      ]⟩,
    ⟨[77493], [77491, 13], .source 38811⟩,
    ⟨[77491, 13], [77493], .contexts [
        ⟨2906, true, false, [], []⟩
      ]⟩,
    ⟨[77493], [77493], .contexts []⟩,
    ⟨[77493], [77493], .contexts []⟩,
    ⟨[77491, 13], [77493], .contexts [
        ⟨2907, false, false, [], []⟩,
        ⟨2908, false, false, [], []⟩,
        ⟨2909, false, false, [], []⟩,
        ⟨2909, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77491], [13, 77491], .contexts []⟩,
    ⟨[13, 77491], [13, 77491], .contexts []⟩,
    ⟨[13, 77491], [13, 77491], .contexts []⟩,
    ⟨[13, 77493], [13, 77493], .contexts []⟩,
    ⟨[13, 77493], [13, 77493], .contexts []⟩,
    ⟨[13, 77493], [13, 77493], .contexts []⟩,
    ⟨[77493, 1], [77493, 1], .contexts []⟩,
    ⟨[77493], [77493], .contexts []⟩,
    ⟨[77493, 1], [13, 77493], .contexts [
        ⟨2917, false, false, [], []⟩,
        ⟨2910, true, false, [], [1]⟩,
        ⟨387, false, false, [77491], []⟩,
        ⟨390, false, false, [77491], []⟩,
        ⟨2828, false, false, [], [13, 1, 13]⟩,
        ⟨2797, false, false, [], [13, 1, 13]⟩,
        ⟨2798, false, false, [], [13, 1, 13]⟩,
        ⟨2798, false, false, [], [13, 1, 13]⟩,
        ⟨2816, false, false, [], [1, 13]⟩,
        ⟨2813, false, false, [], [1, 13]⟩,
        ⟨2815, false, false, [], [1, 13]⟩,
        ⟨2815, false, false, [], [1, 13]⟩,
        ⟨2827, false, false, [13], [13]⟩,
        ⟨2911, false, false, [], [13]⟩,
        ⟨2912, false, false, [], [13]⟩,
        ⟨2913, false, false, [], [13]⟩,
        ⟨2907, false, false, [13], []⟩,
        ⟨2914, false, false, [], []⟩,
        ⟨2915, false, false, [], []⟩,
        ⟨2916, false, false, [], []⟩,
        ⟨2918, false, false, [13], []⟩
      ]⟩,
    ⟨[77493, 1], [13, 77493], .contexts [
        ⟨2919, false, false, [], []⟩,
        ⟨153, true, false, [], [77493]⟩
      ]⟩,
    ⟨[541, 77201], [541, 77201], .contexts []⟩,
    ⟨[541, 77201], [541, 77201], .contexts []⟩,
    ⟨[77493, 3], [77493, 3], .contexts []⟩,
    ⟨[541, 77201], [541, 77201], .contexts [
        ⟨1063, false, false, [541], []⟩
      ]⟩,
    ⟨[541, 77201], [541, 77201], .contexts [
        ⟨2833, true, false, [], [77201]⟩
      ]⟩,
    ⟨[77493, 3], [541, 77201], .contexts [
        ⟨2923, false, false, [], []⟩,
        ⟨2910, true, false, [], [3]⟩,
        ⟨107, false, false, [77491], []⟩,
        ⟨109, false, false, [77491], []⟩,
        ⟨2854, false, false, [], [13]⟩,
        ⟨570, false, false, [541], []⟩,
        ⟨2921, false, false, [], []⟩,
        ⟨2922, false, false, [], []⟩,
        ⟨2924, false, false, [], []⟩,
        ⟨2925, false, false, [], []⟩
      ]⟩,
    ⟨[315, 77491, 13], [315, 77493], .contexts [
        ⟨2907, false, false, [315], []⟩
      ]⟩,
    ⟨[315, 77493], [315, 77493], .contexts []⟩,
    ⟨[315, 77493], [315, 77493], .contexts []⟩,
    ⟨[315, 77493], [315, 77493], .contexts []⟩,
    ⟨[77493, 5], [77493, 5], .contexts []⟩,
    ⟨[245, 77493], [245, 77493], .contexts []⟩,
    ⟨[245, 77493], [245, 77493], .contexts []⟩,
    ⟨[77493, 11], [77493, 11], .contexts []⟩,
    ⟨[77493, 11], [245, 77493], .contexts [
        ⟨2934, false, false, [], []⟩,
        ⟨2910, true, false, [], [11]⟩,
        ⟨137, false, false, [77491], []⟩,
        ⟨138, false, false, [77491], []⟩,
        ⟨2851, false, false, [], [13]⟩,
        ⟨2852, false, false, [], [13]⟩,
        ⟨2849, false, false, [], [13]⟩,
        ⟨2850, false, false, [], [13]⟩,
        ⟨2850, false, false, [], [13]⟩,
        ⟨2907, false, false, [245], []⟩,
        ⟨2932, false, false, [], []⟩,
        ⟨2933, false, false, [], []⟩,
        ⟨2918, false, false, [245], []⟩,
        ⟨1606, true, false, [], [77493]⟩
      ]⟩,
    ⟨[77493, 1], [13, 77493], .contexts [
        ⟨2917, false, false, [], []⟩,
        ⟨2920, false, false, [], []⟩,
        ⟨2914, false, false, [], []⟩,
        ⟨2916, false, false, [], []⟩,
        ⟨2916, false, false, [], []⟩
      ]⟩,
    ⟨[565], [31, 541], .source 347⟩,
    ⟨[77199], [151, 77197], .contexts [
        ⟨565, true, false, [], []⟩,
        ⟨565, true, false, [], []⟩,
        ⟨652, true, false, [], []⟩,
        ⟨1069, true, false, [], []⟩,
        ⟨1004, false, false, [140], [77201, 1]⟩,
        ⟨1063, true, false, [140, 150], [1]⟩,
        ⟨1068, true, false, [140, 150, 77201], [1]⟩,
        ⟨1067, false, false, [140, 150], [1, 1]⟩,
        ⟨18, false, false, [140, 77197], []⟩,
        ⟨970, true, false, [], [77197]⟩,
        ⟨1065, false, false, [], []⟩,
        ⟨1071, true, false, [], [77197]⟩,
        ⟨1070, true, false, [], [77197]⟩,
        ⟨971, true, false, [], [77197]⟩,
        ⟨1066, false, false, [], []⟩
      ]⟩,
    ⟨[567], [565, 151], .source 348⟩,
    ⟨[77493, 3], [541, 77201], .contexts [
        ⟨2926, false, false, [], []⟩
      ]⟩,
    ⟨[569], [541, 151], .source 349⟩,
    ⟨[77197, 3], [77197, 3], .contexts []⟩,
    ⟨[77197], [77197], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 046. -/
def y322TCContextRaw046 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[571], [566], .source 350⟩,
    ⟨[573], [571, 569], .source 351⟩,
    ⟨[77197, 3], [573, 77197], .contexts [
        ⟨2942, false, false, [], []⟩,
        ⟨2939, false, false, [566], [77197, 3]⟩,
        ⟨2938, true, false, [566, 565], [3]⟩,
        ⟨566, true, false, [566, 565], [3]⟩,
        ⟨2937, false, false, [566], [77201, 1, 3]⟩,
        ⟨740, false, false, [566], [541, 77201, 1, 3]⟩,
        ⟨2926, true, false, [566, 13], [1, 3]⟩,
        ⟨2936, true, false, [566], [3, 1, 3]⟩,
        ⟨852, false, false, [566, 77493], []⟩,
        ⟨853, false, false, [566, 77493], []⟩,
        ⟨2923, false, false, [566], [1]⟩,
        ⟨2940, false, false, [566], [1]⟩,
        ⟨2921, false, false, [566], [1]⟩,
        ⟨2922, false, false, [566], [1]⟩,
        ⟨2922, false, false, [566], [1]⟩,
        ⟨566, false, false, [566, 541], []⟩,
        ⟨2938, false, false, [566, 541], []⟩,
        ⟨2941, true, false, [566], [77197]⟩,
        ⟨2943, false, false, [566, 569], []⟩,
        ⟨2944, true, false, [], [569, 77197]⟩,
        ⟨2945, true, false, [], [77197]⟩
      ]⟩,
    ⟨[573, 77197], [573, 77197], .contexts []⟩,
    ⟨[77195, 3], [77195, 3], .contexts []⟩,
    ⟨[77195], [77195], .contexts []⟩,
    ⟨[575], [572], .source 352⟩,
    ⟨[572], [572], .contexts []⟩,
    ⟨[77195, 3], [575, 77195], .contexts [
        ⟨2948, false, false, [], []⟩,
        ⟨559, true, false, [], [3]⟩,
        ⟨2947, true, false, [572], [9, 3]⟩,
        ⟨2947, true, false, [572], [9, 3]⟩,
        ⟨2946, true, false, [572], [9, 3]⟩,
        ⟨2942, true, false, [572], [9, 3]⟩,
        ⟨1010, false, false, [572, 77197], []⟩,
        ⟨77, false, false, [572, 77197], []⟩,
        ⟨654, false, false, [572], []⟩,
        ⟨655, false, false, [572], []⟩,
        ⟨558, false, false, [572], []⟩,
        ⟨558, false, false, [572], []⟩,
        ⟨2949, false, false, [572], []⟩,
        ⟨2951, true, false, [], [77195]⟩,
        ⟨2951, true, false, [], [77195]⟩,
        ⟨2950, true, false, [], [77195]⟩
      ]⟩,
    ⟨[77495], [77493, 15], .source 38812⟩,
    ⟨[77493, 15], [77495], .contexts [
        ⟨2953, true, false, [], []⟩
      ]⟩,
    ⟨[77495, 15], [77493], .contexts [
        ⟨2954, true, false, [], [15]⟩,
        ⟨3, false, false, [77493], []⟩,
        ⟨2909, false, false, [], []⟩
      ]⟩,
    ⟨[77495], [77495], .contexts []⟩,
    ⟨[77495], [77495], .contexts []⟩,
    ⟨[77493, 15], [77495], .contexts [
        ⟨2954, false, false, [], []⟩,
        ⟨2956, false, false, [], []⟩,
        ⟨2957, false, false, [], []⟩,
        ⟨2957, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77495], [13, 77495], .contexts []⟩,
    ⟨[13, 77495], [13, 77495], .contexts []⟩,
    ⟨[77495], [77495], .contexts []⟩,
    ⟨[77495, 1], [13, 77495], .contexts [
        ⟨2958, true, false, [], [1]⟩,
        ⟨17, false, false, [77493], []⟩,
        ⟨21, false, false, [77493], []⟩,
        ⟨2936, false, false, [], [15]⟩,
        ⟨2954, false, false, [13], []⟩,
        ⟨2959, false, false, [], []⟩,
        ⟨2960, false, false, [], []⟩,
        ⟨2961, false, false, [13], []⟩,
        ⟨153, true, false, [], [77495]⟩
      ]⟩,
    ⟨[77493, 5], [315, 77493], .contexts [
        ⟨2931, false, false, [], []⟩,
        ⟨2931, false, false, [], []⟩,
        ⟨2910, true, false, [], [5]⟩,
        ⟨116, false, false, [77491], []⟩,
        ⟨117, false, false, [77491], []⟩,
        ⟨2856, false, false, [], [13]⟩,
        ⟨2927, false, false, [], []⟩,
        ⟨2928, false, false, [], []⟩,
        ⟨2929, false, false, [], []⟩,
        ⟨2930, false, false, [], []⟩,
        ⟨2918, false, false, [315], []⟩,
        ⟨2812, true, false, [], [77493]⟩,
        ⟨2928, false, false, [], []⟩,
        ⟨2930, false, false, [], []⟩,
        ⟨2930, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77495], [245, 77495], .contexts []⟩,
    ⟨[245, 77495], [245, 77495], .contexts []⟩,
    ⟨[77495, 11], [77495, 11], .contexts []⟩,
    ⟨[77495, 11], [245, 77495], .contexts [
        ⟨2966, false, false, [], []⟩,
        ⟨2958, true, false, [], [11]⟩,
        ⟨89, false, false, [77493], []⟩,
        ⟨92, false, false, [77493], []⟩,
        ⟨2934, false, false, [], [15]⟩,
        ⟨2935, false, false, [], [15]⟩,
        ⟨2932, false, false, [], [15]⟩,
        ⟨2933, false, false, [], [15]⟩,
        ⟨2933, false, false, [], [15]⟩,
        ⟨2954, false, false, [245], []⟩,
        ⟨2964, false, false, [], []⟩,
        ⟨2965, false, false, [], []⟩,
        ⟨2961, false, false, [245], []⟩,
        ⟨1606, true, false, [], [77495]⟩
      ]⟩,
    ⟨[77497], [77495, 3], .source 38813⟩,
    ⟨[77495, 3], [77497], .contexts [
        ⟨2968, true, false, [], []⟩
      ]⟩,
    ⟨[77497, 3], [77495], .contexts [
        ⟨2969, true, false, [], [3]⟩,
        ⟨35, false, false, [77495], []⟩,
        ⟨2957, false, false, [], []⟩
      ]⟩,
    ⟨[77497], [77497], .contexts []⟩,
    ⟨[77497], [77497], .contexts []⟩,
    ⟨[77495, 3], [77497], .contexts [
        ⟨2969, false, false, [], []⟩,
        ⟨2971, false, false, [], []⟩,
        ⟨2972, false, false, [], []⟩,
        ⟨2972, false, false, [], []⟩
      ]⟩,
    ⟨[245, 77497], [245, 77497], .contexts []⟩,
    ⟨[245, 77497], [245, 77497], .contexts []⟩,
    ⟨[77497, 11], [77497, 11], .contexts []⟩,
    ⟨[77497], [77497], .contexts []⟩,
    ⟨[77497, 15], [541, 77201], .contexts [
        ⟨2973, true, false, [], [15]⟩,
        ⟨245, false, false, [77495], []⟩,
        ⟨246, false, false, [77495], []⟩,
        ⟨2955, false, false, [], [3]⟩,
        ⟨2908, false, false, [], [3]⟩,
        ⟨2909, false, false, [], [3]⟩,
        ⟨2909, false, false, [], [3]⟩,
        ⟨2940, false, false, [], []⟩,
        ⟨2921, false, false, [], []⟩,
        ⟨2922, false, false, [], []⟩,
        ⟨2922, false, false, [], []⟩,
        ⟨2924, false, false, [], []⟩,
        ⟨2925, false, false, [], []⟩
      ]⟩,
    ⟨[77201, 15], [543, 77497], .contexts [
        ⟨2978, true, false, [540], [15]⟩,
        ⟨3, false, false, [540, 77497], []⟩,
        ⟨2835, true, false, [], [77497]⟩
      ]⟩,
    ⟨[77499], [77497, 5], .source 38814⟩,
    ⟨[77497, 5], [77499], .contexts [
        ⟨2980, true, false, [], []⟩
      ]⟩,
    ⟨[77499, 5], [77497], .contexts [
        ⟨2981, true, false, [], [5]⟩,
        ⟨49, false, false, [77497], []⟩,
        ⟨2972, false, false, [], []⟩
      ]⟩,
    ⟨[77497, 5], [77499], .contexts [
        ⟨2981, false, false, [], []⟩
      ]⟩,
    ⟨[77499], [77499], .contexts []⟩,
    ⟨[77499], [77499], .contexts []⟩,
    ⟨[77499], [77499], .contexts []⟩,
    ⟨[77497, 11, 5], [245, 77499], .contexts [
        ⟨2976, false, false, [], [5]⟩,
        ⟨2976, false, false, [], [5]⟩,
        ⟨2973, true, false, [], [11, 5]⟩,
        ⟨231, false, false, [77495], [5]⟩,
        ⟨232, false, false, [77495], [5]⟩,
        ⟨2966, false, false, [], [3, 5]⟩,
        ⟨2967, false, false, [], [3, 5]⟩,
        ⟨2964, false, false, [], [3, 5]⟩,
        ⟨2965, false, false, [], [3, 5]⟩,
        ⟨2965, false, false, [], [3, 5]⟩,
        ⟨2969, false, false, [245], [5]⟩,
        ⟨2974, false, false, [], [5]⟩,
        ⟨2975, false, false, [], [5]⟩,
        ⟨2977, false, false, [245], [5]⟩,
        ⟨1606, true, false, [], [77497, 5]⟩,
        ⟨2974, false, false, [], [5]⟩,
        ⟨2975, false, false, [], [5]⟩,
        ⟨2975, false, false, [], [5]⟩,
        ⟨2981, false, false, [245], []⟩
      ]⟩,
    ⟨[77501], [77499, 1], .source 38815⟩,
    ⟨[77499, 1], [77501], .contexts [
        ⟨2988, true, false, [], []⟩
      ]⟩,
    ⟨[77501], [77501], .contexts []⟩,
    ⟨[77501], [77501], .contexts []⟩,
    ⟨[77503], [77501, 9], .source 38816⟩,
    ⟨[77501, 9], [77503], .contexts [
        ⟨2992, true, false, [], []⟩
      ]⟩,
    ⟨[77505], [77503, 11], .source 38817⟩,
    ⟨[77503, 11], [77505], .contexts [
        ⟨2994, true, false, [], []⟩
      ]⟩,
    ⟨[77503], [77503], .contexts []⟩,
    ⟨[77505], [77505], .contexts []⟩,
    ⟨[77505], [77505], .contexts []⟩,
    ⟨[77503, 11], [77505], .contexts [
        ⟨2995, false, false, [], []⟩,
        ⟨2997, false, false, [], []⟩,
        ⟨2998, false, false, [], []⟩,
        ⟨2998, false, false, [], []⟩
      ]⟩,
    ⟨[77503, 9], [77501], .contexts [
        ⟨2993, true, false, [], [9]⟩,
        ⟨76, false, false, [77501], []⟩,
        ⟨2991, false, false, [], []⟩
      ]⟩,
    ⟨[77507], [77505, 1], .source 38818⟩,
    ⟨[77505, 1], [77507], .contexts [
        ⟨3001, true, false, [], []⟩
      ]⟩,
    ⟨[77509], [77507, 13], .source 38819⟩,
    ⟨[77507, 13], [77509], .contexts [
        ⟨3003, true, false, [], []⟩
      ]⟩,
    ⟨[77507], [77507], .contexts []⟩,
    ⟨[77511], [77509, 15], .source 38820⟩,
    ⟨[77509, 15], [77511], .contexts [
        ⟨3006, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 047. -/
def y322TCContextRaw047 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77509], [77509], .contexts []⟩,
    ⟨[77513], [77511, 1], .source 38821⟩,
    ⟨[77511, 1], [77513], .contexts [
        ⟨3009, true, false, [], []⟩
      ]⟩,
    ⟨[77511], [77511], .contexts []⟩,
    ⟨[77515], [77513, 3], .source 38822⟩,
    ⟨[77513, 3], [77515], .contexts [
        ⟨3012, true, false, [], []⟩
      ]⟩,
    ⟨[77513], [77513], .contexts []⟩,
    ⟨[77517], [77515, 5], .source 38823⟩,
    ⟨[77515, 5], [77517], .contexts [
        ⟨3015, true, false, [], []⟩
      ]⟩,
    ⟨[77515], [77515], .contexts []⟩,
    ⟨[77517, 5], [77515], .contexts [
        ⟨3016, true, false, [], [5]⟩,
        ⟨49, false, false, [77515], []⟩,
        ⟨3017, false, false, [], []⟩
      ]⟩,
    ⟨[77519], [77517, 1], .source 38824⟩,
    ⟨[77517, 1], [77519], .contexts [
        ⟨3019, true, false, [], []⟩
      ]⟩,
    ⟨[77517], [77517], .contexts []⟩,
    ⟨[77519, 1], [77517], .contexts [
        ⟨3020, true, false, [], [1]⟩,
        ⟨18, false, false, [77517], []⟩,
        ⟨3021, false, false, [], []⟩
      ]⟩,
    ⟨[77521], [77519, 9], .source 38825⟩,
    ⟨[77519, 9], [77521], .contexts [
        ⟨3023, true, false, [], []⟩
      ]⟩,
    ⟨[77519], [77519], .contexts []⟩,
    ⟨[77523], [77521, 11], .source 38826⟩,
    ⟨[77521, 11], [77523], .contexts [
        ⟨3026, true, false, [], []⟩
      ]⟩,
    ⟨[77521], [77521], .contexts []⟩,
    ⟨[77523, 11], [77521], .contexts [
        ⟨3027, true, false, [], [11]⟩,
        ⟨90, false, false, [77521], []⟩,
        ⟨3028, false, false, [], []⟩
      ]⟩,
    ⟨[77525], [77523, 1], .source 38827⟩,
    ⟨[77523, 1], [77525], .contexts [
        ⟨3030, true, false, [], []⟩
      ]⟩,
    ⟨[77523], [77523], .contexts []⟩,
    ⟨[77525, 1], [77523], .contexts [
        ⟨3031, true, false, [], [1]⟩,
        ⟨18, false, false, [77523], []⟩,
        ⟨3032, false, false, [], []⟩
      ]⟩,
    ⟨[77527], [77525, 13], .source 38828⟩,
    ⟨[77525, 13], [77527], .contexts [
        ⟨3034, true, false, [], []⟩
      ]⟩,
    ⟨[77525], [77525], .contexts []⟩,
    ⟨[77529], [77527, 15], .source 38829⟩,
    ⟨[77527, 15], [77529], .contexts [
        ⟨3037, true, false, [], []⟩
      ]⟩,
    ⟨[77527], [77527], .contexts []⟩,
    ⟨[77529, 15], [77527], .contexts [
        ⟨3038, true, false, [], [15]⟩,
        ⟨3, false, false, [77527], []⟩,
        ⟨3039, false, false, [], []⟩
      ]⟩,
    ⟨[77531], [77529, 1], .source 38830⟩,
    ⟨[77529, 1], [77531], .contexts [
        ⟨3041, true, false, [], []⟩
      ]⟩,
    ⟨[77529], [77529], .contexts []⟩,
    ⟨[77533], [77531, 3], .source 38831⟩,
    ⟨[77531, 3], [77533], .contexts [
        ⟨3044, true, false, [], []⟩
      ]⟩,
    ⟨[77531], [77531], .contexts []⟩,
    ⟨[77535], [77533, 5], .source 38832⟩,
    ⟨[77533], [77533], .contexts []⟩,
    ⟨[77537], [77535, 1], .source 38833⟩,
    ⟨[77535], [77535], .contexts []⟩,
    ⟨[77539], [77537, 9], .source 38834⟩,
    ⟨[77537], [77537], .contexts []⟩,
    ⟨[77541], [77539, 11], .source 38835⟩,
    ⟨[77539], [77539], .contexts []⟩,
    ⟨[77543], [77541, 1], .source 38836⟩,
    ⟨[77541], [77541], .contexts []⟩,
    ⟨[77545], [77543, 13], .source 38837⟩,
    ⟨[77543], [77543], .contexts []⟩,
    ⟨[77547], [77545, 15], .source 38838⟩,
    ⟨[77545], [77545], .contexts []⟩,
    ⟨[77549], [77547, 1], .source 38839⟩,
    ⟨[77547], [77547], .contexts []⟩,
    ⟨[77551], [77549, 3], .source 38840⟩,
    ⟨[77549], [77549], .contexts []⟩,
    ⟨[77553], [77551, 5], .source 38841⟩,
    ⟨[77551], [77551], .contexts []⟩,
    ⟨[77555], [77553, 1], .source 38842⟩,
    ⟨[77553], [77553], .contexts []⟩,
    ⟨[77557], [77555, 9], .source 38843⟩,
    ⟨[77555], [77555], .contexts []⟩,
    ⟨[77557, 9], [77555], .contexts [
        ⟨3069, false, false, [], [9]⟩,
        ⟨76, false, false, [77555], []⟩,
        ⟨3070, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 048. -/
def y322TCContextRaw048 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77559], [77557, 11], .source 38844⟩,
    ⟨[77557], [77557], .contexts []⟩,
    ⟨[77559, 11], [77557], .contexts [
        ⟨3072, false, false, [], [11]⟩,
        ⟨90, false, false, [77557], []⟩,
        ⟨3073, false, false, [], []⟩
      ]⟩,
    ⟨[77561], [77559, 1], .source 38845⟩,
    ⟨[77559], [77559], .contexts []⟩,
    ⟨[77561, 1], [77559], .contexts [
        ⟨3075, false, false, [], [1]⟩,
        ⟨18, false, false, [77559], []⟩,
        ⟨3076, false, false, [], []⟩
      ]⟩,
    ⟨[77563], [77561, 13], .source 38846⟩,
    ⟨[77561, 13], [77563], .contexts [
        ⟨3078, true, false, [], []⟩
      ]⟩,
    ⟨[77561], [77561], .contexts []⟩,
    ⟨[77563, 13], [77561], .contexts [
        ⟨3079, true, false, [], [13]⟩,
        ⟨98, false, false, [77561], []⟩,
        ⟨3080, false, false, [], []⟩
      ]⟩,
    ⟨[77565], [77563, 15], .source 38847⟩,
    ⟨[77563, 15], [77565], .contexts [
        ⟨3082, true, false, [], []⟩
      ]⟩,
    ⟨[77563], [77563], .contexts []⟩,
    ⟨[77565, 15], [77563], .contexts [
        ⟨3083, true, false, [], [15]⟩,
        ⟨3, false, false, [77563], []⟩,
        ⟨3084, false, false, [], []⟩
      ]⟩,
    ⟨[77567], [77565, 1], .source 38848⟩,
    ⟨[77565], [77565], .contexts []⟩,
    ⟨[77567, 1], [77565], .contexts [
        ⟨3086, false, false, [], [1]⟩,
        ⟨18, false, false, [77565], []⟩,
        ⟨3087, false, false, [], []⟩
      ]⟩,
    ⟨[77569], [77567, 3], .source 38849⟩,
    ⟨[77567, 3], [77569], .contexts [
        ⟨3089, true, false, [], []⟩
      ]⟩,
    ⟨[77567], [77567], .contexts []⟩,
    ⟨[77569, 3], [77567], .contexts [
        ⟨3090, true, false, [], [3]⟩,
        ⟨35, false, false, [77567], []⟩,
        ⟨3091, false, false, [], []⟩
      ]⟩,
    ⟨[77571], [77569, 5], .source 38850⟩,
    ⟨[77569, 5], [77571], .contexts [
        ⟨3093, true, false, [], []⟩
      ]⟩,
    ⟨[77569], [77569], .contexts []⟩,
    ⟨[77571, 5], [77569], .contexts [
        ⟨3094, true, false, [], [5]⟩,
        ⟨49, false, false, [77569], []⟩,
        ⟨3095, false, false, [], []⟩
      ]⟩,
    ⟨[77573], [77571, 1], .source 38851⟩,
    ⟨[77571], [77571], .contexts []⟩,
    ⟨[77573, 1], [77571], .contexts [
        ⟨3097, false, false, [], [1]⟩,
        ⟨18, false, false, [77571], []⟩,
        ⟨3098, false, false, [], []⟩
      ]⟩,
    ⟨[77575], [77573, 9], .source 38852⟩,
    ⟨[77573], [77573], .contexts []⟩,
    ⟨[77575, 9], [77573], .contexts [
        ⟨3100, false, false, [], [9]⟩,
        ⟨76, false, false, [77573], []⟩,
        ⟨3101, false, false, [], []⟩
      ]⟩,
    ⟨[77577], [77575, 11], .source 38853⟩,
    ⟨[77575, 11], [77577], .contexts [
        ⟨3103, true, false, [], []⟩
      ]⟩,
    ⟨[77575], [77575], .contexts []⟩,
    ⟨[77577, 11], [77575], .contexts [
        ⟨3104, true, false, [], [11]⟩,
        ⟨90, false, false, [77575], []⟩,
        ⟨3105, false, false, [], []⟩
      ]⟩,
    ⟨[77579], [77577, 1], .source 38854⟩,
    ⟨[77577, 1], [77579], .contexts [
        ⟨3107, true, false, [], []⟩
      ]⟩,
    ⟨[77577], [77577], .contexts []⟩,
    ⟨[77579, 1], [77577], .contexts [
        ⟨3108, true, false, [], [1]⟩,
        ⟨18, false, false, [77577], []⟩,
        ⟨3109, false, false, [], []⟩
      ]⟩,
    ⟨[77581], [77579, 13], .source 38855⟩,
    ⟨[77579], [77579], .contexts []⟩,
    ⟨[77581, 13], [77579], .contexts [
        ⟨3111, false, false, [], [13]⟩,
        ⟨98, false, false, [77579], []⟩,
        ⟨3112, false, false, [], []⟩
      ]⟩,
    ⟨[77583], [77581, 15], .source 38856⟩,
    ⟨[77581, 15], [77583], .contexts [
        ⟨3114, true, false, [], []⟩
      ]⟩,
    ⟨[77581], [77581], .contexts []⟩,
    ⟨[77583, 15], [77581], .contexts [
        ⟨3115, true, false, [], [15]⟩,
        ⟨3, false, false, [77581], []⟩,
        ⟨3116, false, false, [], []⟩
      ]⟩,
    ⟨[77585], [77583, 1], .source 38857⟩,
    ⟨[77583, 1], [77585], .contexts [
        ⟨3118, true, false, [], []⟩
      ]⟩,
    ⟨[77583], [77583], .contexts []⟩,
    ⟨[77585, 1], [77583], .contexts [
        ⟨3119, true, false, [], [1]⟩,
        ⟨18, false, false, [77583], []⟩,
        ⟨3120, false, false, [], []⟩
      ]⟩,
    ⟨[77587], [77585, 3], .source 38858⟩,
    ⟨[77585, 3], [77587], .contexts [
        ⟨3122, true, false, [], []⟩
      ]⟩,
    ⟨[77585], [77585], .contexts []⟩,
    ⟨[77587, 3], [77585], .contexts [
        ⟨3123, true, false, [], [3]⟩,
        ⟨35, false, false, [77585], []⟩,
        ⟨3124, false, false, [], []⟩
      ]⟩,
    ⟨[77589], [77587, 5], .source 38859⟩,
    ⟨[77587, 5], [77589], .contexts [
        ⟨3126, true, false, [], []⟩
      ]⟩,
    ⟨[77587], [77587], .contexts []⟩,
    ⟨[77589, 5], [77587], .contexts [
        ⟨3127, true, false, [], [5]⟩,
        ⟨49, false, false, [77587], []⟩,
        ⟨3128, false, false, [], []⟩
      ]⟩,
    ⟨[77591], [77589, 1], .source 38860⟩,
    ⟨[77589], [77589], .contexts []⟩,
    ⟨[77591, 1], [77589], .contexts [
        ⟨3130, false, false, [], [1]⟩,
        ⟨18, false, false, [77589], []⟩,
        ⟨3131, false, false, [], []⟩
      ]⟩,
    ⟨[77593], [77591, 9], .source 38861⟩,
    ⟨[77591], [77591], .contexts []⟩,
    ⟨[77593, 9], [77591], .contexts [
        ⟨3133, false, false, [], [9]⟩,
        ⟨76, false, false, [77591], []⟩,
        ⟨3134, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 049. -/
def y322TCContextRaw049 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77595], [77593, 11], .source 38862⟩,
    ⟨[77593], [77593], .contexts []⟩,
    ⟨[77595, 11], [77593], .contexts [
        ⟨3136, false, false, [], [11]⟩,
        ⟨90, false, false, [77593], []⟩,
        ⟨3137, false, false, [], []⟩
      ]⟩,
    ⟨[77597], [77595, 1], .source 38863⟩,
    ⟨[77595], [77595], .contexts []⟩,
    ⟨[77597, 1], [77595], .contexts [
        ⟨3139, false, false, [], [1]⟩,
        ⟨18, false, false, [77595], []⟩,
        ⟨3140, false, false, [], []⟩
      ]⟩,
    ⟨[77599], [77597, 13], .source 38864⟩,
    ⟨[77597], [77597], .contexts []⟩,
    ⟨[77599, 13], [77597], .contexts [
        ⟨3142, false, false, [], [13]⟩,
        ⟨98, false, false, [77597], []⟩,
        ⟨3143, false, false, [], []⟩
      ]⟩,
    ⟨[77601], [77599, 15], .source 38865⟩,
    ⟨[77599], [77599], .contexts []⟩,
    ⟨[77601, 15], [77599], .contexts [
        ⟨3145, false, false, [], [15]⟩,
        ⟨3, false, false, [77599], []⟩,
        ⟨3146, false, false, [], []⟩
      ]⟩,
    ⟨[77603], [77601, 1], .source 38866⟩,
    ⟨[77601, 1], [77603], .contexts [
        ⟨3148, true, false, [], []⟩
      ]⟩,
    ⟨[77601], [77601], .contexts []⟩,
    ⟨[77603, 1], [77601], .contexts [
        ⟨3149, true, false, [], [1]⟩,
        ⟨18, false, false, [77601], []⟩,
        ⟨3150, false, false, [], []⟩
      ]⟩,
    ⟨[77603], [77603], .contexts []⟩,
    ⟨[77601, 15], [77599], .contexts [
        ⟨3147, false, false, [], []⟩,
        ⟨3146, false, false, [], []⟩,
        ⟨3146, false, false, [], []⟩
      ]⟩,
    ⟨[77597], [77597], .contexts []⟩,
    ⟨[77595], [77595], .contexts []⟩,
    ⟨[77593], [77593], .contexts []⟩,
    ⟨[77591], [77591], .contexts []⟩,
    ⟨[77591, 1], [77589], .contexts [
        ⟨3132, false, false, [], []⟩
      ]⟩,
    ⟨[77589], [77589], .contexts []⟩,
    ⟨[77601, 15, 13, 1, 11, 9, 1], [77589], .contexts [
        ⟨3153, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨3144, false, false, [], [1, 11, 9, 1]⟩,
        ⟨3154, false, false, [], [1, 11, 9, 1]⟩,
        ⟨3143, false, false, [], [1, 11, 9, 1]⟩,
        ⟨3143, false, false, [], [1, 11, 9, 1]⟩,
        ⟨3141, false, false, [], [11, 9, 1]⟩,
        ⟨3155, false, false, [], [11, 9, 1]⟩,
        ⟨3140, false, false, [], [11, 9, 1]⟩,
        ⟨3140, false, false, [], [11, 9, 1]⟩,
        ⟨3138, false, false, [], [9, 1]⟩,
        ⟨3156, false, false, [], [9, 1]⟩,
        ⟨3137, false, false, [], [9, 1]⟩,
        ⟨3137, false, false, [], [9, 1]⟩,
        ⟨3135, false, false, [], [1]⟩,
        ⟨3157, false, false, [], [1]⟩,
        ⟨3134, false, false, [], [1]⟩,
        ⟨3134, false, false, [], [1]⟩,
        ⟨3158, false, false, [], []⟩,
        ⟨3159, false, false, [], []⟩,
        ⟨3131, false, false, [], []⟩,
        ⟨3131, false, false, [], []⟩
      ]⟩,
    ⟨[77589, 5], [77587], .contexts [
        ⟨3129, false, false, [], []⟩
      ]⟩,
    ⟨[77587], [77587], .contexts []⟩,
    ⟨[77587, 3], [77585], .contexts [
        ⟨3125, false, false, [], []⟩
      ]⟩,
    ⟨[77585], [77585], .contexts []⟩,
    ⟨[77585, 1], [77583], .contexts [
        ⟨3121, false, false, [], []⟩
      ]⟩,
    ⟨[77583], [77583], .contexts []⟩,
    ⟨[77583, 15], [77581], .contexts [
        ⟨3117, false, false, [], []⟩
      ]⟩,
    ⟨[77581], [77581], .contexts []⟩,
    ⟨[77581, 13], [77579], .contexts [
        ⟨3113, false, false, [], []⟩
      ]⟩,
    ⟨[77579], [77579], .contexts []⟩,
    ⟨[77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [77579], .contexts [
        ⟨3160, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨3161, false, false, [], [3, 1, 15, 13]⟩,
        ⟨3162, false, false, [], [3, 1, 15, 13]⟩,
        ⟨3128, false, false, [], [3, 1, 15, 13]⟩,
        ⟨3128, false, false, [], [3, 1, 15, 13]⟩,
        ⟨3163, false, false, [], [1, 15, 13]⟩,
        ⟨3164, false, false, [], [1, 15, 13]⟩,
        ⟨3124, false, false, [], [1, 15, 13]⟩,
        ⟨3124, false, false, [], [1, 15, 13]⟩,
        ⟨3165, false, false, [], [15, 13]⟩,
        ⟨3166, false, false, [], [15, 13]⟩,
        ⟨3120, false, false, [], [15, 13]⟩,
        ⟨3120, false, false, [], [15, 13]⟩,
        ⟨3167, false, false, [], [13]⟩,
        ⟨3168, false, false, [], [13]⟩,
        ⟨3116, false, false, [], [13]⟩,
        ⟨3116, false, false, [], [13]⟩,
        ⟨3169, false, false, [], []⟩,
        ⟨3170, false, false, [], []⟩,
        ⟨3112, false, false, [], []⟩,
        ⟨3112, false, false, [], []⟩
      ]⟩,
    ⟨[77579, 1], [77577], .contexts [
        ⟨3110, false, false, [], []⟩
      ]⟩,
    ⟨[77577], [77577], .contexts []⟩,
    ⟨[77577, 11], [77575], .contexts [
        ⟨3106, false, false, [], []⟩
      ]⟩,
    ⟨[77575], [77575], .contexts []⟩,
    ⟨[77575, 9], [77573], .contexts [
        ⟨3102, false, false, [], []⟩
      ]⟩,
    ⟨[77573], [77573], .contexts []⟩,
    ⟨[77573, 1], [77571], .contexts [
        ⟨3099, false, false, [], []⟩
      ]⟩,
    ⟨[77571], [77571], .contexts []⟩,
    ⟨[77571, 5], [77569], .contexts [
        ⟨3096, false, false, [], []⟩
      ]⟩,
    ⟨[77569], [77569], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [77569], .contexts [
        ⟨3171, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨3172, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3173, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3109, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3109, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3174, false, false, [], [9, 1, 5]⟩,
        ⟨3175, false, false, [], [9, 1, 5]⟩,
        ⟨3105, false, false, [], [9, 1, 5]⟩,
        ⟨3105, false, false, [], [9, 1, 5]⟩,
        ⟨3176, false, false, [], [1, 5]⟩,
        ⟨3177, false, false, [], [1, 5]⟩,
        ⟨3101, false, false, [], [1, 5]⟩,
        ⟨3101, false, false, [], [1, 5]⟩,
        ⟨3178, false, false, [], [5]⟩,
        ⟨3179, false, false, [], [5]⟩,
        ⟨3098, false, false, [], [5]⟩,
        ⟨3098, false, false, [], [5]⟩,
        ⟨3180, false, false, [], []⟩,
        ⟨3181, false, false, [], []⟩,
        ⟨3095, false, false, [], []⟩,
        ⟨3095, false, false, [], []⟩
      ]⟩,
    ⟨[77569, 3], [77567], .contexts [
        ⟨3092, false, false, [], []⟩
      ]⟩,
    ⟨[77567], [77567], .contexts []⟩,
    ⟨[77567, 1], [77565], .contexts [
        ⟨3088, false, false, [], []⟩
      ]⟩,
    ⟨[77565], [77565], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [77559], .contexts [
        ⟨3182, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨3183, false, false, [], [1, 15, 13, 1]⟩,
        ⟨3184, false, false, [], [1, 15, 13, 1]⟩,
        ⟨3091, false, false, [], [1, 15, 13, 1]⟩,
        ⟨3091, false, false, [], [1, 15, 13, 1]⟩,
        ⟨3185, false, false, [], [15, 13, 1]⟩,
        ⟨3186, false, false, [], [15, 13, 1]⟩,
        ⟨3087, false, false, [], [15, 13, 1]⟩,
        ⟨3087, false, false, [], [15, 13, 1]⟩,
        ⟨3085, false, false, [], [13, 1]⟩,
        ⟨3084, false, false, [], [13, 1]⟩,
        ⟨3084, false, false, [], [13, 1]⟩,
        ⟨3081, false, false, [], [1]⟩,
        ⟨3080, false, false, [], [1]⟩,
        ⟨3080, false, false, [], [1]⟩,
        ⟨3077, false, false, [], []⟩,
        ⟨3076, false, false, [], []⟩,
        ⟨3076, false, false, [], []⟩
      ]⟩,
    ⟨[77555, 1], [77553], .contexts [
        ⟨3067, false, false, [], [1]⟩,
        ⟨18, false, false, [77553], []⟩,
        ⟨3068, false, false, [], []⟩
      ]⟩,
    ⟨[77553], [77553], .contexts []⟩,
    ⟨[77553, 5], [77551], .contexts [
        ⟨3065, false, false, [], [5]⟩,
        ⟨49, false, false, [77551], []⟩,
        ⟨3066, false, false, [], []⟩
      ]⟩,
    ⟨[77551], [77551], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [77549], .contexts [
        ⟨3187, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨3074, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3073, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3073, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3071, false, false, [], [1, 5, 3]⟩,
        ⟨3070, false, false, [], [1, 5, 3]⟩,
        ⟨3070, false, false, [], [1, 5, 3]⟩,
        ⟨3188, false, false, [], [5, 3]⟩,
        ⟨3189, false, false, [], [5, 3]⟩,
        ⟨3068, false, false, [], [5, 3]⟩,
        ⟨3068, false, false, [], [5, 3]⟩,
        ⟨3190, false, false, [], [3]⟩,
        ⟨3191, false, false, [], [3]⟩,
        ⟨3066, false, false, [], [3]⟩,
        ⟨3066, false, false, [], [3]⟩,
        ⟨3063, false, false, [], [3]⟩,
        ⟨35, false, false, [77549], []⟩,
        ⟨3064, false, false, [], []⟩,
        ⟨3064, false, false, [], []⟩,
        ⟨3064, false, false, [], []⟩
      ]⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [77541], .contexts [
        ⟨3192, false, false, [], [1, 15, 13, 1]⟩,
        ⟨3061, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [77547], [15, 13, 1]⟩,
        ⟨3062, false, false, [], [15, 13, 1]⟩,
        ⟨3062, false, false, [], [15, 13, 1]⟩,
        ⟨3062, false, false, [], [15, 13, 1]⟩,
        ⟨3059, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [77545], [13, 1]⟩,
        ⟨3060, false, false, [], [13, 1]⟩,
        ⟨3060, false, false, [], [13, 1]⟩,
        ⟨3060, false, false, [], [13, 1]⟩,
        ⟨3057, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [77543], [1]⟩,
        ⟨3058, false, false, [], [1]⟩,
        ⟨3058, false, false, [], [1]⟩,
        ⟨3058, false, false, [], [1]⟩,
        ⟨3055, false, false, [], [1]⟩,
        ⟨18, false, false, [77541], []⟩,
        ⟨3056, false, false, [], []⟩,
        ⟨3056, false, false, [], []⟩,
        ⟨3056, false, false, [], []⟩
      ]⟩,
    ⟨[77533], [77533], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [77533], .contexts [
        ⟨3193, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3053, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [77539], [9, 1, 5]⟩,
        ⟨3054, false, false, [], [9, 1, 5]⟩,
        ⟨3054, false, false, [], [9, 1, 5]⟩,
        ⟨3054, false, false, [], [9, 1, 5]⟩,
        ⟨3051, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [77537], [1, 5]⟩,
        ⟨3052, false, false, [], [1, 5]⟩,
        ⟨3052, false, false, [], [1, 5]⟩,
        ⟨3052, false, false, [], [1, 5]⟩,
        ⟨3049, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [77535], [5]⟩,
        ⟨3050, false, false, [], [5]⟩,
        ⟨3050, false, false, [], [5]⟩,
        ⟨3050, false, false, [], [5]⟩,
        ⟨3047, false, false, [], [5]⟩,
        ⟨49, false, false, [77533], []⟩,
        ⟨3048, false, false, [], []⟩,
        ⟨3194, false, false, [], []⟩,
        ⟨3048, false, false, [], []⟩,
        ⟨3048, false, false, [], []⟩
      ]⟩,
    ⟨[77529], [77529], .contexts []⟩,
    ⟨[77527], [77527], .contexts []⟩,
    ⟨[77525], [77525], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [77525], .contexts [
        ⟨3195, false, false, [], [3, 1, 15, 13]⟩,
        ⟨3045, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [77531], [1, 15, 13]⟩,
        ⟨3046, false, false, [], [1, 15, 13]⟩,
        ⟨3046, false, false, [], [1, 15, 13]⟩,
        ⟨3046, false, false, [], [1, 15, 13]⟩,
        ⟨3042, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [77529], [15, 13]⟩,
        ⟨3043, false, false, [], [15, 13]⟩,
        ⟨3196, false, false, [], [15, 13]⟩,
        ⟨3043, false, false, [], [15, 13]⟩,
        ⟨3043, false, false, [], [15, 13]⟩,
        ⟨3040, false, false, [], [13]⟩,
        ⟨3197, false, false, [], [13]⟩,
        ⟨3039, false, false, [], [13]⟩,
        ⟨3039, false, false, [], [13]⟩,
        ⟨3035, true, false, [], [13]⟩,
        ⟨98, false, false, [77525], []⟩,
        ⟨3036, false, false, [], []⟩,
        ⟨3198, false, false, [], []⟩,
        ⟨3036, false, false, [], []⟩,
        ⟨3036, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 050. -/
def y322TCContextRaw050 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77523], [77523], .contexts []⟩,
    ⟨[77515], [77515], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [77515], .contexts [
        ⟨3199, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨3033, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3200, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3032, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3032, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3029, false, false, [], [9, 1, 5]⟩,
        ⟨3028, false, false, [], [9, 1, 5]⟩,
        ⟨3028, false, false, [], [9, 1, 5]⟩,
        ⟨3024, true, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [77519], [1, 5]⟩,
        ⟨3025, false, false, [], [1, 5]⟩,
        ⟨3025, false, false, [], [1, 5]⟩,
        ⟨3025, false, false, [], [1, 5]⟩,
        ⟨3022, false, false, [], [5]⟩,
        ⟨3021, false, false, [], [5]⟩,
        ⟨3021, false, false, [], [5]⟩,
        ⟨3018, false, false, [], []⟩,
        ⟨3201, false, false, [], []⟩,
        ⟨3017, false, false, [], []⟩,
        ⟨3017, false, false, [], []⟩
      ]⟩,
    ⟨[77511], [77511], .contexts []⟩,
    ⟨[77509], [77509], .contexts []⟩,
    ⟨[77507], [77507], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [77507], .contexts [
        ⟨3202, false, false, [], [3, 1, 15, 13]⟩,
        ⟨3013, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [77513], [1, 15, 13]⟩,
        ⟨3014, false, false, [], [1, 15, 13]⟩,
        ⟨3014, false, false, [], [1, 15, 13]⟩,
        ⟨3014, false, false, [], [1, 15, 13]⟩,
        ⟨3010, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [77511], [15, 13]⟩,
        ⟨3011, false, false, [], [15, 13]⟩,
        ⟨3203, false, false, [], [15, 13]⟩,
        ⟨3011, false, false, [], [15, 13]⟩,
        ⟨3011, false, false, [], [15, 13]⟩,
        ⟨3007, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [77509], [13]⟩,
        ⟨3008, false, false, [], [13]⟩,
        ⟨3204, false, false, [], [13]⟩,
        ⟨3008, false, false, [], [13]⟩,
        ⟨3008, false, false, [], [13]⟩,
        ⟨3004, true, false, [], [13]⟩,
        ⟨98, false, false, [77507], []⟩,
        ⟨3005, false, false, [], []⟩,
        ⟨3205, false, false, [], []⟩,
        ⟨3005, false, false, [], []⟩,
        ⟨3005, false, false, [], []⟩
      ]⟩,
    ⟨[77503], [77503], .contexts []⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [77499], .contexts [
        ⟨3206, false, false, [], [1, 11, 9, 1]⟩,
        ⟨3002, true, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [77505], [11, 9, 1]⟩,
        ⟨2998, false, false, [], [11, 9, 1]⟩,
        ⟨2997, false, false, [], [11, 9, 1]⟩,
        ⟨2998, false, false, [], [11, 9, 1]⟩,
        ⟨2998, false, false, [], [11, 9, 1]⟩,
        ⟨2995, true, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [77503], [9, 1]⟩,
        ⟨2996, false, false, [], [9, 1]⟩,
        ⟨3207, false, false, [], [9, 1]⟩,
        ⟨2996, false, false, [], [9, 1]⟩,
        ⟨2996, false, false, [], [9, 1]⟩,
        ⟨3000, false, false, [], [1]⟩,
        ⟨2990, false, false, [], [1]⟩,
        ⟨2991, false, false, [], [1]⟩,
        ⟨2991, false, false, [], [1]⟩,
        ⟨2989, true, false, [], [1]⟩,
        ⟨18, false, false, [77499], []⟩,
        ⟨2985, false, false, [], []⟩,
        ⟨2984, false, false, [], []⟩,
        ⟨2985, false, false, [], []⟩,
        ⟨2985, false, false, [], []⟩
      ]⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [13, 77491], .contexts [
        ⟨3208, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨2982, false, false, [], [3, 1, 15, 13]⟩,
        ⟨2971, false, false, [], [3, 1, 15, 13]⟩,
        ⟨2972, false, false, [], [3, 1, 15, 13]⟩,
        ⟨2972, false, false, [], [3, 1, 15, 13]⟩,
        ⟨2970, false, false, [], [1, 15, 13]⟩,
        ⟨2956, false, false, [], [1, 15, 13]⟩,
        ⟨2957, false, false, [], [1, 15, 13]⟩,
        ⟨2957, false, false, [], [1, 15, 13]⟩,
        ⟨2962, false, false, [], [15, 13]⟩,
        ⟨2959, false, false, [], [15, 13]⟩,
        ⟨2960, false, false, [], [15, 13]⟩,
        ⟨2960, false, false, [], [15, 13]⟩,
        ⟨2955, false, false, [13], [13]⟩,
        ⟨2914, false, false, [], [13]⟩,
        ⟨2915, false, false, [], [13]⟩,
        ⟨2916, false, false, [], [13]⟩,
        ⟨2907, true, false, [13], [13]⟩,
        ⟨98, false, false, [13, 77491], []⟩,
        ⟨2829, false, false, [13], []⟩,
        ⟨2911, false, false, [], []⟩,
        ⟨2912, false, false, [], []⟩,
        ⟨2913, false, false, [], []⟩
      ]⟩,
    ⟨[577], [31, 245], .source 353⟩,
    ⟨[579], [577, 317], .source 354⟩,
    ⟨[581], [579, 317], .source 355⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [581, 77123], .contexts [
        ⟨3209, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨2828, false, false, [13], [11, 9, 1, 5]⟩,
        ⟨2813, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2814, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2815, false, false, [], [11, 9, 1, 5]⟩,
        ⟨2825, false, false, [13], [9, 1, 5]⟩,
        ⟨740, true, false, [], [245, 77489, 9, 1, 5]⟩,
        ⟨3210, true, false, [], [77489, 9, 1, 5]⟩,
        ⟨2796, false, false, [577], [1, 5]⟩,
        ⟨1945, false, false, [577], [5]⟩,
        ⟨3211, true, false, [], [77123, 5]⟩,
        ⟨1962, false, false, [579], []⟩,
        ⟨3212, true, false, [], [77123]⟩
      ]⟩,
    ⟨[583], [581, 323], .source 356⟩,
    ⟨[585], [583, 315], .source 357⟩,
    ⟨[587], [585, 505], .source 358⟩,
    ⟨[589], [587, 257], .source 359⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [589, 77485], .contexts [
        ⟨3213, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨1957, false, false, [581], [1, 15, 13, 1]⟩,
        ⟨3214, true, false, [], [77123, 1, 15, 13, 1]⟩,
        ⟨429, false, false, [583], [15, 13, 1]⟩,
        ⟨1942, false, false, [583], [15, 13, 1]⟩,
        ⟨3215, true, false, [], [77119, 15, 13, 1]⟩,
        ⟨2772, false, false, [585], [13, 1]⟩,
        ⟨3216, true, false, [], [77487, 13, 1]⟩,
        ⟨2755, false, false, [587], [1]⟩,
        ⟨2685, false, false, [587], []⟩,
        ⟨3217, true, false, [], [77485]⟩
      ]⟩,
    ⟨[591], [589, 265], .source 360⟩,
    ⟨[593], [591, 257], .source 361⟩,
    ⟨[595], [593, 261], .source 362⟩,
    ⟨[597], [595, 249], .source 363⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [597, 77355], .contexts [
        ⟨3218, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨2676, false, false, [589], [9, 1, 5, 3]⟩,
        ⟨1574, false, false, [589], [1, 5, 3]⟩,
        ⟨3219, true, false, [], [77349, 1, 5, 3]⟩,
        ⟨1566, false, false, [591], [5, 3]⟩,
        ⟨3220, true, false, [], [77349, 5, 3]⟩,
        ⟨1571, false, false, [593], [3]⟩,
        ⟨3221, true, false, [], [77349, 3]⟩,
        ⟨1559, false, false, [595], []⟩,
        ⟨3222, true, false, [], [77355]⟩
      ]⟩,
    ⟨[599], [597, 209], .source 364⟩,
    ⟨[601], [599, 31], .source 365⟩,
    ⟨[603], [601, 19], .source 366⟩,
    ⟨[605], [603, 211], .source 367⟩,
    ⟨[607], [605, 209], .source 368⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [607, 77113], .contexts [
        ⟨3223, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨1493, false, false, [597], [15, 13, 1, 11]⟩,
        ⟨3224, true, false, [], [77109, 15, 13, 1, 11]⟩,
        ⟨326, false, false, [599], [13, 1, 11]⟩,
        ⟨740, true, false, [599], [77109, 13, 1, 11]⟩,
        ⟨3225, true, false, [], [77109, 13, 1, 11]⟩,
        ⟨318, false, false, [601], [1, 11]⟩,
        ⟨735, true, false, [601], [77109, 1, 11]⟩,
        ⟨3226, true, false, [], [77109, 1, 11]⟩,
        ⟨1491, false, false, [603], [11]⟩,
        ⟨3227, true, false, [], [77355, 11]⟩,
        ⟨1525, false, false, [605], []⟩,
        ⟨3228, true, false, [], [77113]⟩
      ]⟩,
    ⟨[609], [607, 29], .source 369⟩,
    ⟨[611], [609, 399], .source 370⟩,
    ⟨[613], [611, 395], .source 371⟩,
    ⟨[615], [613, 387], .source 372⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [615, 77475], .contexts [
        ⟨3229, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨1131, false, false, [607], [1, 5, 3, 1]⟩,
        ⟨1149, false, false, [607], [5, 3, 1]⟩,
        ⟨744, true, false, [607], [77237, 5, 3, 1]⟩,
        ⟨3230, true, false, [], [77237, 5, 3, 1]⟩,
        ⟨2428, false, false, [609], [3, 1]⟩,
        ⟨3231, true, false, [], [77475, 3, 1]⟩,
        ⟨2421, false, false, [611], [1]⟩,
        ⟨3232, true, false, [], [77475, 1]⟩,
        ⟨2295, false, false, [613], []⟩,
        ⟨2412, false, false, [613], []⟩,
        ⟨3233, true, false, [], [77475]⟩
      ]⟩,
    ⟨[617], [615, 423], .source 373⟩,
    ⟨[619], [617, 417], .source 374⟩,
    ⟨[621], [619, 141], .source 375⟩,
    ⟨[623], [621, 137], .source 376⟩,
    ⟨[
      77601, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9
    ], [623, 77211], .contexts [
        ⟨3234, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨2449, false, false, [615], [13, 1, 11, 9]⟩,
        ⟨3235, true, false, [], [77475, 13, 1, 11, 9]⟩,
        ⟨2445, false, false, [617], [1, 11, 9]⟩,
        ⟨3236, true, false, [], [77213, 1, 11, 9]⟩,
        ⟨589, false, false, [619], [11, 9]⟩,
        ⟨1005, false, false, [619], [9]⟩,
        ⟨3237, true, false, [], [77211, 9]⟩,
        ⟨1024, false, false, [621], []⟩,
        ⟨3238, true, false, [], [77211]⟩
      ]⟩,
    ⟨[625], [623, 293], .source 377⟩,
    ⟨[1, 3], [
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4
    ], .contexts [
        ⟨764, false, false, [], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4
        ]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨149, false, false, [], [
          0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
          0
        ]⟩,
        ⟨19, false, false, [15, 13], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [15, 13, 1], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [15, 13, 1, 11], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [15, 13, 1, 11, 9], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [15, 13, 1, 11, 9, 1], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [15, 13, 1, 11, 9, 1, 5], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [15, 13, 1, 11, 9, 1, 5, 3], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [15, 13, 1, 11, 9, 1, 5, 3, 1], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [10, 8, 0]⟩,
        ⟨91, false, false, [15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [8, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨3242, false, false, [], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨3243, false, false, [], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨3244, false, false, [], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨3245, false, false, [], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨3246, false, false, [], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨3247, false, false, [], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0]⟩,
        ⟨91, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0]⟩,
        ⟨77, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11
        ], [0]⟩
      ]⟩,
    ⟨[
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4
    ], [
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], .contexts [
        ⟨3248, false, false, [], [4]⟩,
        ⟨19, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4]⟩,
        ⟨50, false, false, [
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], []⟩
      ]⟩,
    ⟨[77603, 3], [77603, 3], .contexts []⟩,
    ⟨[77603, 3], [625, 77241], .contexts [
        ⟨3250, false, false, [], []⟩,
        ⟨3152, true, false, [], [3]⟩,
        ⟨3152, true, false, [], [3]⟩,
        ⟨3149, true, false, [], [3]⟩,
        ⟨3241, false, false, [77601], []⟩,
        ⟨3249, false, false, [77601], []⟩,
        ⟨3239, false, false, [], [1, 5]⟩,
        ⟨587, false, false, [623], [5]⟩,
        ⟨1855, false, false, [623], []⟩,
        ⟨3240, true, false, [], [77241]⟩,
        ⟨1604, false, false, [625], []⟩,
        ⟨24, true, false, [], [625, 77241]⟩
      ]⟩,
    ⟨[627], [624], .source 378⟩,
    ⟨[77241, 3], [627, 77603], .contexts [
        ⟨3251, true, false, [624], [3]⟩,
        ⟨35, false, false, [624, 77603], []⟩,
        ⟨3252, true, false, [], [77603]⟩
      ]⟩,
    ⟨[77603, 1], [77601], .contexts [
        ⟨3151, false, false, [], []⟩,
        ⟨3150, false, false, [], []⟩,
        ⟨3150, false, false, [], []⟩
      ]⟩,
    ⟨[625, 77241], [625, 77241], .contexts []⟩,
    ⟨[77603, 3], [625, 77241], .contexts [
        ⟨3250, false, false, [], []⟩,
        ⟨3251, false, false, [], []⟩,
        ⟨3255, false, false, [], []⟩,
        ⟨3255, false, false, [], []⟩
      ]⟩,
    ⟨[629], [625, 295], .source 379⟩,
    ⟨[629, 77205], [629, 77205], .contexts []⟩,
    ⟨[629, 77205], [629, 77205], .contexts []⟩,
    ⟨[77601, 3], [77601, 3], .contexts []⟩,
    ⟨[77601, 3], [629, 77205], .contexts [
        ⟨3260, false, false, [], []⟩,
        ⟨3254, true, false, [], [3]⟩,
        ⟨1824, false, false, [77603], []⟩,
        ⟨1826, false, false, [77603], []⟩,
        ⟨3256, false, false, [], [1, 3, 1]⟩,
        ⟨1863, false, false, [625], [3, 1]⟩,
        ⟨3257, true, false, [], [77209, 3, 1]⟩,
        ⟨581, false, false, [629], [1]⟩,
        ⟨578, false, false, [629], []⟩,
        ⟨3258, false, false, [], []⟩,
        ⟨3259, false, false, [], []⟩,
        ⟨1050, false, false, [629], []⟩,
        ⟨24, true, false, [], [629, 77205]⟩
      ]⟩,
    ⟨[631], [628], .source 380⟩,
    ⟨[77205, 3], [631, 77601], .contexts [
        ⟨3261, true, false, [628], [3]⟩,
        ⟨35, false, false, [628, 77601], []⟩,
        ⟨3262, true, false, [], [77601]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 051. -/
def y322TCContextRaw051 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[633], [629, 145], .source 381⟩,
    ⟨[635], [633, 293], .source 382⟩,
    ⟨[637], [635, 627], .source 383⟩,
    ⟨[77603, 3, 5, 3, 5, 3], [637, 77603], .contexts [
        ⟨3256, false, false, [], [5, 3, 5, 3]⟩,
        ⟨1855, true, false, [625, 292], [5, 3, 5, 3]⟩,
        ⟨49, false, false, [625, 292, 77213], [3, 5, 3]⟩,
        ⟨1856, true, false, [625], [77213, 3, 5, 3]⟩,
        ⟨3257, true, false, [], [77213, 3, 5, 3]⟩,
        ⟨1014, false, false, [629], [5, 3]⟩,
        ⟨3264, true, false, [], [77213, 5, 3]⟩,
        ⟨1855, false, false, [633], [3]⟩,
        ⟨3265, true, false, [], [77241, 3]⟩,
        ⟨3253, false, false, [635], []⟩,
        ⟨3266, true, false, [], [77603]⟩
      ]⟩,
    ⟨[3, 5, 3, 5, 3, 5], [], .contexts [
        ⟨1478, false, false, [], []⟩
      ]⟩,
    ⟨[77603], [77603], .contexts []⟩,
    ⟨[77603, 5], [77603, 5], .contexts []⟩,
    ⟨[77603], [77603], .contexts []⟩,
    ⟨[639], [636], .source 384⟩,
    ⟨[636], [636], .contexts []⟩,
    ⟨[77603, 5], [639, 77603], .contexts [
        ⟨3270, false, false, [], []⟩,
        ⟨3267, true, false, [636], [5]⟩,
        ⟨3268, false, false, [636, 77603], []⟩,
        ⟨3269, false, false, [636], []⟩,
        ⟨3271, false, false, [636], []⟩,
        ⟨3273, true, false, [], [77603]⟩,
        ⟨3273, true, false, [], [77603]⟩,
        ⟨3272, true, false, [], [77603]⟩
      ]⟩,
    ⟨[641], [625, 243], .source 385⟩,
    ⟨[643], [641, 505], .source 386⟩,
    ⟨[77487, 9], [77487, 9], .contexts []⟩,
    ⟨[645], [642], .source 387⟩,
    ⟨[642], [642], .contexts []⟩,
    ⟨[77487, 9], [645, 77603], .contexts [
        ⟨3277, false, false, [], []⟩,
        ⟨3276, false, false, [642], [77487, 9]⟩,
        ⟨2691, false, false, [642, 641], [77487, 9]⟩,
        ⟨35, true, false, [642, 641, 502, 77487], [9]⟩,
        ⟨2762, false, false, [642, 641, 502], [3, 9]⟩,
        ⟨3275, false, false, [642], [77115, 3, 9]⟩,
        ⟨1544, false, false, [642, 625], [77115, 3, 9]⟩,
        ⟨76, true, false, [642, 625, 244, 77115], [3, 9]⟩,
        ⟨1608, false, false, [642, 625, 244], [9, 3, 9]⟩,
        ⟨3256, true, false, [642], [9, 3, 9]⟩,
        ⟨2706, false, false, [642, 77603], []⟩,
        ⟨3269, false, false, [642], []⟩,
        ⟨3271, false, false, [642], []⟩,
        ⟨3279, true, false, [], [77603]⟩,
        ⟨3279, true, false, [], [77603]⟩,
        ⟨3278, true, false, [], [77603]⟩
      ]⟩,
    ⟨[643], [644], .contexts [
        ⟨3278, true, true, [], []⟩
      ]⟩,
    ⟨[77603, 9], [643, 77487], .contexts [
        ⟨3280, true, false, [644], [9]⟩,
        ⟨76, false, false, [644, 77487], []⟩,
        ⟨3281, true, false, [], [77487]⟩
      ]⟩,
    ⟨[647], [625, 245], .source 388⟩,
    ⟨[649], [647, 627], .source 389⟩,
    ⟨[77603, 11], [77603, 11], .contexts []⟩,
    ⟨[651], [648], .source 390⟩,
    ⟨[648], [648], .contexts []⟩,
    ⟨[77603, 11], [651, 77603], .contexts [
        ⟨3285, false, false, [], []⟩,
        ⟨3284, false, false, [648], [77603, 11]⟩,
        ⟨3253, true, false, [648, 647], [11]⟩,
        ⟨3283, false, false, [648], [77241, 3, 11]⟩,
        ⟨1612, true, false, [648, 625], [3, 11]⟩,
        ⟨3256, true, false, [648], [11, 3, 11]⟩,
        ⟨2823, false, false, [648, 77603], []⟩,
        ⟨3269, false, false, [648], []⟩,
        ⟨3271, false, false, [648], []⟩,
        ⟨3287, true, false, [], [77603]⟩,
        ⟨3287, true, false, [], [77603]⟩,
        ⟨3286, true, false, [], [77603]⟩
      ]⟩,
    ⟨[653], [641, 399], .source 391⟩,
    ⟨[3, 13, 3, 13], [], .contexts [
        ⟨237, false, false, [], []⟩
      ]⟩,
    ⟨[77471, 13], [77471, 13], .contexts []⟩,
    ⟨[655], [652], .source 392⟩,
    ⟨[652], [652], .contexts []⟩,
    ⟨[77471, 13], [655, 77603], .contexts [
        ⟨3291, false, false, [], []⟩,
        ⟨3289, false, false, [652], [77471, 13]⟩,
        ⟨2432, true, false, [652, 641], [13]⟩,
        ⟨3275, false, false, [652], [77237, 3, 13]⟩,
        ⟨1547, true, false, [652, 625], [3, 13]⟩,
        ⟨1169, true, false, [652, 625], [3, 13]⟩,
        ⟨3256, true, false, [652], [13, 3, 13]⟩,
        ⟨3290, false, false, [652, 77603], []⟩,
        ⟨3269, false, false, [652], []⟩,
        ⟨3271, false, false, [652], []⟩,
        ⟨3293, true, false, [], [77603]⟩,
        ⟨3293, true, false, [], [77603]⟩,
        ⟨3292, true, false, [], [77603]⟩
      ]⟩,
    ⟨[653], [654], .contexts [
        ⟨3292, true, true, [], []⟩
      ]⟩,
    ⟨[657], [640], .source 393⟩,
    ⟨[640], [640], .contexts []⟩,
    ⟨[77601, 3], [629, 77205], .contexts [
        ⟨3260, false, false, [], []⟩,
        ⟨3261, false, false, [], []⟩,
        ⟨3258, false, false, [], []⟩,
        ⟨3259, false, false, [], []⟩,
        ⟨3259, false, false, [], []⟩
      ]⟩,
    ⟨[659], [629, 151], .source 394⟩,
    ⟨[661], [659, 631], .source 395⟩,
    ⟨[77601], [77601], .contexts []⟩,
    ⟨[77601, 11], [77601, 11], .contexts []⟩,
    ⟨[77601], [77601], .contexts []⟩,
    ⟨[663], [660], .source 396⟩,
    ⟨[660], [660], .contexts []⟩,
    ⟨[77601, 11], [663, 77601], .contexts [
        ⟨3302, false, false, [], []⟩,
        ⟨3300, false, false, [660], [77601, 11]⟩,
        ⟨3263, true, false, [660, 659], [11]⟩,
        ⟨3299, false, false, [660], [77205, 3, 11]⟩,
        ⟨1051, true, false, [660, 629], [3, 11]⟩,
        ⟨3298, true, false, [660], [11, 3, 11]⟩,
        ⟨2823, false, false, [660, 77601], []⟩,
        ⟨3301, false, false, [660], []⟩,
        ⟨3303, false, false, [660], []⟩,
        ⟨3305, true, false, [], [77601]⟩,
        ⟨3305, true, false, [], [77601]⟩,
        ⟨3304, true, false, [], [77601]⟩
      ]⟩,
    ⟨[665], [629, 543], .source 397⟩,
    ⟨[667], [664], .source 398⟩,
    ⟨[667], [664], .contexts [
        ⟨3308, false, false, [], []⟩
      ]⟩,
    ⟨[664], [664], .contexts []⟩,
    ⟨[665], [666], .contexts [
        ⟨3308, true, true, [], []⟩
      ]⟩,
    ⟨[77599], [665, 77491], .contexts [
        ⟨3153, true, false, [], []⟩,
        ⟨3309, false, false, [666], [77601, 15]⟩,
        ⟨3310, false, false, [666], [77601, 15]⟩,
        ⟨3310, false, false, [666], [77601, 15]⟩,
        ⟨3303, true, false, [666, 664], [15]⟩,
        ⟨3301, true, false, [666, 664], [15]⟩,
        ⟨2767, true, false, [666, 664, 77601], [15]⟩,
        ⟨3298, false, false, [666, 664], [15, 3, 15, 15]⟩,
        ⟨574, false, false, [666, 664, 629], [3, 15, 15]⟩,
        ⟨2834, true, false, [666, 664, 629, 540], [3, 15, 15]⟩,
        ⟨35, false, false, [666, 664, 629, 540, 77491], [15, 15]⟩,
        ⟨2835, true, false, [666, 664, 629], [77491, 15, 15]⟩,
        ⟨3307, true, false, [666, 664], [77491, 15, 15]⟩,
        ⟨3, false, false, [666, 77491], []⟩,
        ⟨3311, true, false, [], [77491]⟩
      ]⟩,
    ⟨[77599], [665, 77491], .contexts [
        ⟨3312, false, false, [], []⟩
      ]⟩,
    ⟨[665, 77493], [665, 77493], .contexts []⟩,
    ⟨[669], [665, 31], .source 399⟩,
    ⟨[671], [668], .source 400⟩,
    ⟨[77493], [671, 77595], .contexts [
        ⟨3315, false, false, [668], [77493]⟩,
        ⟨740, false, false, [668, 665], [77493]⟩,
        ⟨2920, true, false, [668, 665], []⟩,
        ⟨3314, true, false, [668], [1]⟩,
        ⟨3311, false, false, [668], [77493, 1]⟩,
        ⟨3314, true, false, [668, 666, 664], [1]⟩,
        ⟨2907, true, false, [668, 666], [1]⟩,
        ⟨3313, true, false, [668, 666, 664], [13, 1]⟩,
        ⟨3144, false, false, [668, 666, 664], [1]⟩,
        ⟨3154, false, false, [668, 666, 664], [1]⟩,
        ⟨24, true, false, [668, 666, 664], [77597, 1]⟩,
        ⟨3309, true, false, [668, 666], [77597, 1]⟩,
        ⟨3141, false, false, [668], []⟩,
        ⟨3155, false, false, [668], []⟩,
        ⟨24, true, false, [668], [77595]⟩,
        ⟨3316, true, false, [], [77595]⟩
      ]⟩,
    ⟨[673], [669, 245], .source 401⟩,
    ⟨[675], [672], .source 402⟩,
    ⟨[675], [672], .contexts [
        ⟨3319, false, false, [], []⟩
      ]⟩,
    ⟨[672], [672], .contexts []⟩,
    ⟨[77493, 9], [675, 77591], .contexts [
        ⟨3319, true, true, [672], [77493, 9]⟩,
        ⟨3318, false, false, [672, 674, 672], [77493, 9]⟩,
        ⟨2935, true, false, [672, 674, 672, 669], [9]⟩,
        ⟨3316, true, true, [672, 674, 672], [77493, 11, 9]⟩,
        ⟨3317, false, false, [672, 674, 672, 670], [11, 9]⟩,
        ⟨3138, false, false, [672, 674, 672], [9]⟩,
        ⟨3156, false, false, [672, 674, 672], [9]⟩,
        ⟨24, true, false, [672, 674, 672], [77593, 9]⟩,
        ⟨3320, true, false, [672, 674], [77593, 9]⟩,
        ⟨3135, false, false, [672], []⟩,
        ⟨3157, false, false, [672], []⟩,
        ⟨3321, true, false, [], [77591]⟩,
        ⟨3321, true, false, [], [77591]⟩,
        ⟨3320, true, false, [], [77591]⟩
      ]⟩,
    ⟨[639, 77603], [639, 77603], .contexts []⟩,
    ⟨[638], [638], .contexts []⟩,
    ⟨[645, 77603], [645, 77603], .contexts []⟩,
    ⟨[9, 1, 9], [0, 8, 0], .contexts [
        ⟨884, false, false, [], [0, 8, 0]⟩
      ]⟩,
    ⟨[77601, 9], [77601, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 052. -/
def y322TCContextRaw052 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[677], [643, 261], .source 403⟩,
    ⟨[77601, 9], [677, 77337], .contexts [
        ⟨3327, false, false, [], []⟩,
        ⟨3151, true, false, [], [9]⟩,
        ⟨3325, true, false, [644], [1, 9]⟩,
        ⟨3325, true, false, [644], [1, 9]⟩,
        ⟨3280, true, false, [644], [1, 9]⟩,
        ⟨3277, true, false, [644], [1, 9]⟩,
        ⟨3326, false, false, [644, 77487], []⟩,
        ⟨1145, false, false, [644, 77487], []⟩,
        ⟨2775, false, false, [644], [9, 1]⟩,
        ⟨1367, false, false, [644], [9, 1]⟩,
        ⟨1337, false, false, [644], [9, 1]⟩,
        ⟨1337, false, false, [644], [9, 1]⟩,
        ⟨1368, false, false, [644], [1]⟩,
        ⟨1369, false, false, [644], [1]⟩,
        ⟨1333, false, false, [644], [1]⟩,
        ⟨1333, false, false, [644], [1]⟩,
        ⟨1371, false, false, [644], []⟩,
        ⟨2628, false, false, [644], []⟩,
        ⟨1700, false, false, [644], []⟩,
        ⟨1700, false, false, [644], []⟩,
        ⟨2629, false, false, [644, 261], []⟩,
        ⟨3281, true, false, [], [261, 77337]⟩,
        ⟨3328, true, false, [], [77337]⟩
      ]⟩,
    ⟨[679], [676], .source 404⟩,
    ⟨[77337, 9], [679, 77601], .contexts [
        ⟨3329, true, false, [676], [9]⟩,
        ⟨76, false, false, [676, 77601], []⟩,
        ⟨3330, true, false, [], [77601]⟩
      ]⟩,
    ⟨[655, 77603], [655, 77603], .contexts []⟩,
    ⟨[439, 77467, 13], [439, 77465], .contexts [
        ⟨2279, false, false, [439], []⟩
      ]⟩,
    ⟨[439, 77465], [439, 77465], .contexts []⟩,
    ⟨[439, 77465], [439, 77465], .contexts []⟩,
    ⟨[439, 77465], [439, 77465], .contexts []⟩,
    ⟨[681], [439, 461], .source 405⟩,
    ⟨[13, 1, 13], [0, 12, 0], .contexts [
        ⟨386, false, false, [], [0, 12, 0]⟩
      ]⟩,
    ⟨[77601, 13], [77601, 13], .contexts []⟩,
    ⟨[683], [653, 681], .source 406⟩,
    ⟨[77601, 13], [683, 77461], .contexts [
        ⟨3339, false, false, [], []⟩,
        ⟨3151, true, false, [], [13]⟩,
        ⟨3332, true, false, [654], [1, 13]⟩,
        ⟨3332, true, false, [654], [1, 13]⟩,
        ⟨3294, true, false, [654], [1, 13]⟩,
        ⟨3291, true, false, [654], [1, 13]⟩,
        ⟨3338, false, false, [654, 77471], []⟩,
        ⟨389, false, false, [654, 77471], []⟩,
        ⟨2510, false, false, [654], [13, 1]⟩,
        ⟨3333, false, false, [654], [1]⟩,
        ⟨3334, false, false, [654], [1]⟩,
        ⟨3335, false, false, [654], [1]⟩,
        ⟨3336, false, false, [654], [1]⟩,
        ⟨2275, false, false, [654, 439], []⟩,
        ⟨2547, false, false, [654, 439], []⟩,
        ⟨3337, true, false, [654], [77461]⟩,
        ⟨2732, false, false, [654, 681], []⟩,
        ⟨3295, true, false, [], [681, 77461]⟩,
        ⟨3340, true, false, [], [77461]⟩
      ]⟩,
    ⟨[685], [682], .source 407⟩,
    ⟨[77461, 13], [685, 77601], .contexts [
        ⟨3341, true, false, [682], [13]⟩,
        ⟨98, false, false, [682, 77601], []⟩,
        ⟨3342, true, false, [], [77601]⟩
      ]⟩,
    ⟨[687], [31, 675], .source 408⟩,
    ⟨[675, 77591], [675, 77591], .contexts []⟩,
    ⟨[77493, 9], [675, 77591], .contexts [
        ⟨3322, false, false, [], []⟩,
        ⟨3345, false, false, [], []⟩,
        ⟨3345, false, false, [], []⟩
      ]⟩,
    ⟨[77589, 9], [77589, 9], .contexts []⟩,
    ⟨[689], [686], .source 409⟩,
    ⟨[691], [689, 675], .source 410⟩,
    ⟨[315, 77493, 9], [315, 675, 77591], .contexts [
        ⟨3322, false, false, [315], []⟩
      ]⟩,
    ⟨[315, 675, 77591], [315, 675, 77591], .contexts []⟩,
    ⟨[315, 675, 77591], [315, 675, 77591], .contexts []⟩,
    ⟨[693], [315, 675], .source 411⟩,
    ⟨[315, 675, 77591], [693, 77591], .contexts [
        ⟨3353, true, false, [], [77591]⟩
      ]⟩,
    ⟨[77591, 5], [77591, 5], .contexts []⟩,
    ⟨[77591], [77591], .contexts []⟩,
    ⟨[695], [692], .source 412⟩,
    ⟨[695], [692], .contexts [
        ⟨3357, false, false, [], []⟩
      ]⟩,
    ⟨[697], [695, 675], .source 413⟩,
    ⟨[77591, 5], [697, 77591], .contexts [
        ⟨3355, false, false, [], []⟩,
        ⟨3354, true, false, [692], [5]⟩,
        ⟨3352, true, false, [692], [5]⟩,
        ⟨3351, true, false, [692], [5]⟩,
        ⟨3350, true, false, [692], [5]⟩,
        ⟨2963, true, false, [692], [9, 5]⟩,
        ⟨1672, false, false, [692, 77493], []⟩,
        ⟨77, false, false, [692, 77493], []⟩,
        ⟨3346, false, false, [692], []⟩,
        ⟨3356, false, false, [692, 675], []⟩,
        ⟨3358, true, false, [], [675, 77591]⟩,
        ⟨3359, true, false, [], [77591]⟩
      ]⟩,
    ⟨[677, 77337], [677, 77337], .contexts []⟩,
    ⟨[77601, 9], [677, 77337], .contexts [
        ⟨3327, false, false, [], []⟩,
        ⟨3329, false, false, [], []⟩,
        ⟨3361, false, false, [], []⟩,
        ⟨3361, false, false, [], []⟩
      ]⟩,
    ⟨[699], [677, 501], .source 414⟩,
    ⟨[77333, 9], [77333, 9], .contexts []⟩,
    ⟨[701], [698], .source 415⟩,
    ⟨[703], [701, 629], .source 416⟩,
    ⟨[77333, 9], [703, 77205], .contexts [
        ⟨3364, false, false, [], []⟩,
        ⟨3363, false, false, [698], [77333, 9]⟩,
        ⟨2640, true, false, [698, 677], [9]⟩,
        ⟨1324, true, false, [698, 677], [9]⟩,
        ⟨3362, true, false, [698], [3, 9]⟩,
        ⟨841, false, false, [698, 77601], []⟩,
        ⟨36, false, false, [698, 77601], []⟩,
        ⟨3298, false, false, [698], []⟩,
        ⟨1050, false, false, [698, 629], []⟩,
        ⟨3365, true, false, [], [629, 77205]⟩,
        ⟨3366, true, false, [], [77205]⟩
      ]⟩,
    ⟨[705], [702], .source 417⟩,
    ⟨[77205, 9], [705, 77333], .contexts [
        ⟨3367, true, false, [702], [9]⟩,
        ⟨76, false, false, [702, 77333], []⟩,
        ⟨3368, true, false, [], [77333]⟩
      ]⟩,
    ⟨[683, 77461], [683, 77461], .contexts []⟩,
    ⟨[707], [683, 531], .source 418⟩,
    ⟨[77337, 13], [77337, 13], .contexts []⟩,
    ⟨[77455], [77455], .contexts []⟩,
    ⟨[709], [679, 707], .source 419⟩,
    ⟨[77337, 13], [709, 77455], .contexts [
        ⟨3372, false, false, [], []⟩,
        ⟨3362, true, false, [676], [13]⟩,
        ⟨315, false, false, [676, 77601], []⟩,
        ⟨316, false, false, [676, 77601], []⟩,
        ⟨3339, false, false, [676], [9]⟩,
        ⟨3341, false, false, [676], [9]⟩,
        ⟨3370, false, false, [676], [9]⟩,
        ⟨3370, false, false, [676], [9]⟩,
        ⟨2269, false, false, [676, 683], []⟩,
        ⟨2737, false, false, [676, 683], []⟩,
        ⟨3371, true, false, [676], [77455]⟩,
        ⟨3373, false, false, [676, 707], []⟩,
        ⟨3330, true, false, [], [707, 77455]⟩,
        ⟨3374, true, false, [], [77455]⟩
      ]⟩,
    ⟨[711], [708], .source 420⟩,
    ⟨[691, 77589], [691, 77589], .contexts []⟩,
    ⟨[77589, 9], [691, 77589], .contexts [
        ⟨3347, false, false, [], []⟩,
        ⟨3347, false, false, [], []⟩,
        ⟨3132, true, false, [], [9]⟩,
        ⟨3344, false, false, [686], [77591, 1, 9]⟩,
        ⟨740, false, false, [686], [675, 77591, 1, 9]⟩,
        ⟨3322, true, false, [686, 13], [1, 9]⟩,
        ⟨2936, true, false, [686], [9, 1, 9]⟩,
        ⟨1022, false, false, [686, 77493], []⟩,
        ⟨787, false, false, [686, 77493], []⟩,
        ⟨3346, false, false, [686], [1]⟩,
        ⟨3132, false, false, [686, 675], []⟩,
        ⟨3348, true, false, [], [675, 77589]⟩,
        ⟨3349, true, false, [], [77589]⟩,
        ⟨3377, false, false, [], []⟩,
        ⟨3377, false, false, [], []⟩
      ]⟩,
    ⟨[77587, 9], [77587, 9], .contexts []⟩,
    ⟨[77587], [77587], .contexts []⟩,
    ⟨[713], [690], .source 421⟩,
    ⟨[690], [690], .contexts []⟩,
    ⟨[77587, 9], [713, 77587], .contexts [
        ⟨3379, false, false, [], []⟩,
        ⟨3129, true, false, [], [9]⟩,
        ⟨3378, true, false, [690], [5, 9]⟩,
        ⟨1034, false, false, [690, 77589], []⟩,
        ⟨50, false, false, [690, 77589], []⟩,
        ⟨3161, false, false, [690], []⟩,
        ⟨3162, false, false, [690], []⟩,
        ⟨3128, false, false, [690], []⟩,
        ⟨3128, false, false, [690], []⟩,
        ⟨3380, false, false, [690], []⟩,
        ⟨3382, true, false, [], [77587]⟩,
        ⟨3382, true, false, [], [77587]⟩,
        ⟨3381, true, false, [], [77587]⟩
      ]⟩,
    ⟨[697, 77591], [697, 77591], .contexts []⟩,
    ⟨[697, 77587], [697, 77587], .contexts []⟩,
    ⟨[697, 77587], [697, 77587], .contexts []⟩,
    ⟨[715], [696], .source 422⟩,
    ⟨[696], [696], .contexts []⟩,
    ⟨[77587, 1], [715, 77591], .contexts [
        ⟨3386, true, false, [696], [1]⟩,
        ⟨3385, true, false, [696], [1]⟩,
        ⟨3129, true, false, [], [1]⟩,
        ⟨3132, true, false, [], [5, 1]⟩,
        ⟨3384, true, false, [696], [1, 5, 1]⟩,
        ⟨3384, true, false, [696], [1, 5, 1]⟩,
        ⟨3360, true, false, [696], [1, 5, 1]⟩,
        ⟨3355, true, false, [696], [1, 5, 1]⟩,
        ⟨1485, false, false, [696, 77591], []⟩,
        ⟨3356, false, false, [696], []⟩,
        ⟨3388, true, false, [], [77591]⟩,
        ⟨3388, true, false, [], [77591]⟩,
        ⟨3387, true, false, [], [77591]⟩
      ]⟩,
    ⟨[77591, 1], [77589], .contexts [
        ⟨3158, false, false, [], []⟩
      ]⟩,
    ⟨[77589], [697, 77587], .contexts [
        ⟨3131, true, false, [], []⟩,
        ⟨3131, true, false, [], []⟩,
        ⟨3159, true, false, [], []⟩,
        ⟨3390, true, false, [], []⟩,
        ⟨3389, true, false, [714], [1]⟩,
        ⟨18, false, false, [714, 77587], []⟩,
        ⟨3387, false, true, [], [77587]⟩,
        ⟨3385, false, false, [], []⟩,
        ⟨3386, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 053. -/
def y322TCContextRaw053 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[703, 77205], [703, 77205], .contexts []⟩,
    ⟨[77203, 9], [77203, 9], .contexts []⟩,
    ⟨[702], [702], .contexts []⟩,
    ⟨[77203, 9], [705, 77331], .contexts [
        ⟨3393, false, false, [], []⟩,
        ⟨574, true, false, [], [9]⟩,
        ⟨3392, true, false, [702], [15, 9]⟩,
        ⟨3392, true, false, [702], [15, 9]⟩,
        ⟨3367, true, false, [702], [15, 9]⟩,
        ⟨3364, true, false, [702], [15, 9]⟩,
        ⟨1636, false, false, [702, 77333], []⟩,
        ⟨20, false, false, [702, 77333], []⟩,
        ⟨2638, false, false, [702], []⟩,
        ⟨2645, false, false, [702], []⟩,
        ⟨3394, true, false, [], [77331]⟩,
        ⟨3394, true, false, [], [77331]⟩,
        ⟨3368, true, false, [], [77331]⟩
      ]⟩,
    ⟨[709, 77455], [709, 77455], .contexts []⟩,
    ⟨[77453, 13], [77453, 13], .contexts []⟩,
    ⟨[77333], [77333], .contexts []⟩,
    ⟨[717], [711, 501], .source 423⟩,
    ⟨[77453, 13], [717, 77333], .contexts [
        ⟨3397, false, false, [], []⟩,
        ⟨2260, true, false, [], [13]⟩,
        ⟨3396, true, false, [708], [3, 13]⟩,
        ⟨3396, true, false, [708], [3, 13]⟩,
        ⟨3375, true, false, [708], [3, 13]⟩,
        ⟨3372, true, false, [708], [3, 13]⟩,
        ⟨1881, false, false, [708, 77337], []⟩,
        ⟨36, false, false, [708, 77337], []⟩,
        ⟨2634, false, false, [708], []⟩,
        ⟨2641, false, false, [708], []⟩,
        ⟨2639, false, false, [708], []⟩,
        ⟨2639, false, false, [708], []⟩,
        ⟨3398, false, false, [708, 501], []⟩,
        ⟨3376, true, false, [], [501, 77333]⟩,
        ⟨3399, true, false, [], [77333]⟩
      ]⟩,
    ⟨[719], [716], .source 424⟩,
    ⟨[77333, 13], [719, 77453], .contexts [
        ⟨3400, true, false, [716], [13]⟩,
        ⟨98, false, false, [716, 77453], []⟩,
        ⟨3401, true, false, [], [77453]⟩
      ]⟩,
    ⟨[713, 77587], [713, 77587], .contexts []⟩,
    ⟨[77585, 9], [77585, 9], .contexts []⟩,
    ⟨[77585], [77585], .contexts []⟩,
    ⟨[712], [712], .contexts []⟩,
    ⟨[705, 77331], [705, 77331], .contexts []⟩,
    ⟨[77203, 9], [705, 77331], .contexts [
        ⟨3393, false, false, [], []⟩,
        ⟨3395, false, false, [], []⟩,
        ⟨3407, false, false, [], []⟩,
        ⟨3407, false, false, [], []⟩
      ]⟩,
    ⟨[77331, 5], [77331, 5], .contexts []⟩,
    ⟨[703], [704], .contexts [
        ⟨3368, true, true, [], []⟩
      ]⟩,
    ⟨[721], [703, 293], .source 425⟩,
    ⟨[77331, 5], [721, 77253], .contexts [
        ⟨3409, false, false, [], []⟩,
        ⟨3408, true, false, [704], [5]⟩,
        ⟨1805, false, false, [704, 77203], []⟩,
        ⟨1806, false, false, [704, 77203], []⟩,
        ⟨1911, false, false, [704], [9]⟩,
        ⟨1907, false, false, [704], [9]⟩,
        ⟨1908, false, false, [704], [9]⟩,
        ⟨1908, false, false, [704], [9]⟩,
        ⟨1195, false, false, [704, 293], []⟩,
        ⟨1719, false, false, [704, 293], []⟩,
        ⟨3410, true, false, [], [293, 77253]⟩,
        ⟨3411, true, false, [], [77253]⟩
      ]⟩,
    ⟨[723], [720], .source 426⟩,
    ⟨[77253, 5], [723, 77331], .contexts [
        ⟨3412, true, false, [720], [5]⟩,
        ⟨49, false, false, [720, 77331], []⟩,
        ⟨3413, true, false, [], [77331]⟩
      ]⟩,
    ⟨[77329, 9], [77329, 9], .contexts []⟩,
    ⟨[704], [704], .contexts []⟩,
    ⟨[77329, 9], [703, 77201], .contexts [
        ⟨3415, false, false, [], []⟩,
        ⟨1313, true, false, [], [9]⟩,
        ⟨3408, true, false, [704], [13, 9]⟩,
        ⟨926, false, false, [704, 77203], []⟩,
        ⟨1061, false, false, [704], []⟩,
        ⟨1059, false, false, [704], []⟩,
        ⟨1063, false, false, [704], []⟩,
        ⟨3416, true, false, [], [77201]⟩,
        ⟨3416, true, false, [], [77201]⟩,
        ⟨3410, true, false, [], [77201]⟩
      ]⟩,
    ⟨[717, 77333], [717, 77333], .contexts []⟩,
    ⟨[725], [717, 501], .source 427⟩,
    ⟨[727], [725, 719], .source 428⟩,
    ⟨[77453, 1], [77451], .contexts [
        ⟨2317, false, false, [], []⟩,
        ⟨2318, false, false, [], []⟩,
        ⟨2255, false, false, [], []⟩,
        ⟨2255, false, false, [], []⟩
      ]⟩,
    ⟨[13, 1, 13, 1, 13], [0], .contexts [
        ⟨386, false, false, [], [0]⟩
      ]⟩,
    ⟨[77453, 0], [77453, 1], .contexts [
        ⟨19, false, false, [77453], []⟩
      ]⟩,
    ⟨[727, 77451, 13], [77451], .contexts [
        ⟨2256, true, false, [727], [13]⟩,
        ⟨3420, false, false, [], [77453, 1, 13]⟩,
        ⟨3402, true, false, [725], [1, 13]⟩,
        ⟨3419, false, false, [], [77333, 13, 1, 13]⟩,
        ⟨2640, true, false, [717], [13, 1, 13]⟩,
        ⟨1319, true, false, [717], [13, 1, 13]⟩,
        ⟨3418, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3418, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3400, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3397, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [77453], []⟩,
        ⟨3423, false, false, [], []⟩,
        ⟨3421, false, false, [], []⟩
      ]⟩,
    ⟨[77451, 13], [77451, 13], .contexts []⟩,
    ⟨[729], [726], .source 429⟩,
    ⟨[726], [726], .contexts []⟩,
    ⟨[729], [726], .contexts [
        ⟨3426, false, false, [], []⟩,
        ⟨3427, false, false, [], []⟩,
        ⟨3427, false, false, [], []⟩
      ]⟩,
    ⟨[77451, 13], [729, 77451], .contexts [
        ⟨3425, false, false, [], []⟩,
        ⟨3424, false, false, [726], []⟩,
        ⟨2744, false, false, [726], []⟩,
        ⟨3428, true, false, [], [77451]⟩
      ]⟩,
    ⟨[703, 77201], [703, 77201], .contexts []⟩,
    ⟨[77329, 9], [703, 77201], .contexts [
        ⟨3415, false, false, [], []⟩,
        ⟨3417, false, false, [], []⟩,
        ⟨3430, false, false, [], []⟩,
        ⟨3430, false, false, [], []⟩
      ]⟩,
    ⟨[731], [703, 151], .source 430⟩,
    ⟨[77193, 9], [77193, 9], .contexts []⟩,
    ⟨[733], [730], .source 431⟩,
    ⟨[730], [730], .contexts []⟩,
    ⟨[77193, 9], [733, 77327], .contexts [
        ⟨3433, false, false, [], []⟩,
        ⟨555, true, false, [], [9]⟩,
        ⟨559, true, false, [], [1, 9]⟩,
        ⟨3432, false, false, [730], [77197, 9, 1, 9]⟩,
        ⟨2938, true, false, [730, 703], [9, 1, 9]⟩,
        ⟨566, true, false, [730, 703], [9, 1, 9]⟩,
        ⟨3431, true, false, [730], [1, 9, 1, 9]⟩,
        ⟨885, false, false, [730, 77329], []⟩,
        ⟨19, false, false, [730, 77329], []⟩,
        ⟨1380, false, false, [730], []⟩,
        ⟨1381, false, false, [730], []⟩,
        ⟨1308, false, false, [730], []⟩,
        ⟨1308, false, false, [730], []⟩,
        ⟨2648, false, false, [730], []⟩,
        ⟨3435, true, false, [], [77327]⟩,
        ⟨3435, true, false, [], [77327]⟩,
        ⟨3434, true, false, [], [77327]⟩
      ]⟩,
    ⟨[77327, 9], [731, 77193], .contexts [
        ⟨3436, true, false, [732], [9]⟩,
        ⟨76, false, false, [732, 77193], []⟩,
        ⟨3434, false, true, [], [77193]⟩
      ]⟩,
    ⟨[735], [703, 543], .source 432⟩,
    ⟨[737], [735, 675], .source 433⟩,
    ⟨[77591, 3], [77591, 3], .contexts []⟩,
    ⟨[77329], [77329], .contexts []⟩,
    ⟨[739], [736], .source 434⟩,
    ⟨[736], [736], .contexts []⟩,
    ⟨[77591, 3], [739, 77329], .contexts [
        ⟨3440, false, false, [], []⟩,
        ⟨3439, false, false, [736], [77591, 3]⟩,
        ⟨3322, true, false, [736, 735], [3]⟩,
        ⟨3438, false, false, [736], [77493, 9, 3]⟩,
        ⟨2835, false, false, [736, 703], [77493, 9, 3]⟩,
        ⟨35, true, false, [736, 703, 540, 77493], [9, 3]⟩,
        ⟨2926, false, false, [736, 703, 540], [3, 9, 3]⟩,
        ⟨3431, true, false, [736], [3, 9, 3]⟩,
        ⟨2415, false, false, [736, 77329], []⟩,
        ⟨3441, false, false, [736], []⟩,
        ⟨3443, true, false, [], [77329]⟩,
        ⟨3443, true, false, [], [77329]⟩,
        ⟨3442, true, false, [], [77329]⟩
      ]⟩,
    ⟨[737], [738], .contexts [
        ⟨3442, true, true, [], []⟩
      ]⟩,
    ⟨[77329, 3], [737, 77591], .contexts [
        ⟨3444, true, false, [738], [3]⟩,
        ⟨35, false, false, [738, 77591], []⟩,
        ⟨3445, true, false, [], [77591]⟩
      ]⟩,
    ⟨[729, 77451], [729, 77451], .contexts []⟩,
    ⟨[77451, 13], [729, 77451], .contexts [
        ⟨3425, false, false, [], []⟩,
        ⟨3429, false, false, [], []⟩,
        ⟨3447, false, false, [], []⟩,
        ⟨3447, false, false, [], []⟩
      ]⟩,
    ⟨[13, 15, 13, 15], [14, 12], .contexts [
        ⟨147, false, false, [], [14, 12]⟩
      ]⟩,
    ⟨[77447, 15], [77447, 15], .contexts []⟩,
    ⟨[727], [728], .contexts [
        ⟨3426, true, true, [], []⟩
      ]⟩,
    ⟨[727], [727], .contexts []⟩,
    ⟨[728], [728], .contexts []⟩,
    ⟨[727], [728], .contexts [
        ⟨3452, false, false, [], []⟩,
        ⟨3451, false, false, [], []⟩,
        ⟨3453, false, false, [], []⟩,
        ⟨3453, false, false, [], []⟩
      ]⟩,
    ⟨[77193, 9], [733, 77327], .contexts [
        ⟨3436, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 054. -/
def y322TCContextRaw054 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[733, 77327], [733, 77327], .contexts []⟩,
    ⟨[733, 77327], [733, 77327], .contexts []⟩,
    ⟨[741], [733, 499], .source 435⟩,
    ⟨[743], [741, 731], .source 436⟩,
    ⟨[77193, 13], [77193, 13], .contexts []⟩,
    ⟨[77193], [77193], .contexts []⟩,
    ⟨[745], [742], .source 437⟩,
    ⟨[742], [742], .contexts []⟩,
    ⟨[745], [742], .contexts [
        ⟨3462, false, false, [], []⟩,
        ⟨3463, false, false, [], []⟩,
        ⟨3463, false, false, [], []⟩
      ]⟩,
    ⟨[739, 77329], [739, 77329], .contexts []⟩,
    ⟨[77591, 1], [697, 77587], .contexts [
        ⟨3390, false, false, [], []⟩,
        ⟨3391, false, false, [], []⟩,
        ⟨3386, false, false, [], []⟩,
        ⟨3386, false, false, [], []⟩
      ]⟩,
    ⟨[77327, 3], [77327, 3], .contexts []⟩,
    ⟨[77583], [77583], .contexts []⟩,
    ⟨[747], [737, 697], .source 438⟩,
    ⟨[77327, 3], [747, 77583], .contexts [
        ⟨3467, false, false, [], []⟩,
        ⟨1309, true, false, [], [3]⟩,
        ⟨3465, true, false, [738], [1, 3]⟩,
        ⟨3465, true, false, [738], [1, 3]⟩,
        ⟨3444, true, false, [738], [1, 3]⟩,
        ⟨3440, true, false, [738], [1, 3]⟩,
        ⟨2742, false, false, [738, 77591], []⟩,
        ⟨215, false, false, [738, 77591], []⟩,
        ⟨3466, false, false, [738], [3, 1]⟩,
        ⟨3125, false, false, [738, 697], [1]⟩,
        ⟨3121, false, false, [738, 697], []⟩,
        ⟨3468, false, false, [738, 697], []⟩,
        ⟨3445, true, false, [], [697, 77583]⟩,
        ⟨3469, true, false, [], [77583]⟩
      ]⟩,
    ⟨[749], [746], .source 439⟩,
    ⟨[77583, 3], [749, 77327], .contexts [
        ⟨3470, true, false, [746], [3]⟩,
        ⟨35, false, false, [746, 77327], []⟩,
        ⟨3471, true, false, [], [77327]⟩
      ]⟩,
    ⟨[727, 77447], [727, 77447], .contexts []⟩,
    ⟨[77447, 15], [727, 77447], .contexts [
        ⟨3450, false, false, [], []⟩,
        ⟨3450, false, false, [], []⟩,
        ⟨2248, true, false, [], [15]⟩,
        ⟨2252, true, false, [], [13, 15]⟩,
        ⟨3448, true, false, [728], [15, 13, 15]⟩,
        ⟨3449, false, false, [728, 77451], []⟩,
        ⟨149, false, false, [728, 77451], []⟩,
        ⟨2746, false, false, [728], [13]⟩,
        ⟨2321, false, false, [728], []⟩,
        ⟨2322, false, false, [728], []⟩,
        ⟨2247, false, false, [728], []⟩,
        ⟨2247, false, false, [728], []⟩,
        ⟨2752, false, false, [728], []⟩,
        ⟨3454, true, false, [], [77447]⟩,
        ⟨3473, false, false, [], []⟩,
        ⟨3473, false, false, [], []⟩
      ]⟩,
    ⟨[77447, 1], [77445], .contexts [
        ⟨2323, false, false, [], []⟩,
        ⟨2324, false, false, [], []⟩,
        ⟨2243, false, false, [], []⟩,
        ⟨2243, false, false, [], []⟩
      ]⟩,
    ⟨[77445, 15], [77445, 15], .contexts []⟩,
    ⟨[77445], [77445], .contexts []⟩,
    ⟨[77193, 13], [745, 77193], .contexts [
        ⟨3460, false, false, [], []⟩,
        ⟨3459, false, false, [742], [77193, 13]⟩,
        ⟨3437, true, false, [742, 741], [13]⟩,
        ⟨3458, false, false, [742], [77327, 9, 13]⟩,
        ⟨2651, true, false, [742, 733], [9, 13]⟩,
        ⟨3457, true, false, [742], [13, 9, 13]⟩,
        ⟨3457, true, false, [742], [13, 9, 13]⟩,
        ⟨3456, true, false, [742], [13, 9, 13]⟩,
        ⟨3455, true, false, [742], [13, 9, 13]⟩,
        ⟨3433, true, false, [742], [13, 9, 13]⟩,
        ⟨828, false, false, [742, 77193], []⟩,
        ⟨3461, false, false, [742], []⟩,
        ⟨3464, true, false, [], [77193]⟩
      ]⟩,
    ⟨[745, 77193], [745, 77193], .contexts []⟩,
    ⟨[77193, 5], [77191], .contexts [
        ⟨657, false, false, [], []⟩,
        ⟨658, false, false, [], []⟩,
        ⟨550, false, false, [], []⟩,
        ⟨550, false, false, [], []⟩
      ]⟩,
    ⟨[77191, 13], [77191, 13], .contexts []⟩,
    ⟨[77191], [77191], .contexts []⟩,
    ⟨[744], [744], .contexts []⟩,
    ⟨[77191, 13], [743, 77191], .contexts [
        ⟨3481, false, false, [], []⟩,
        ⟨551, true, false, [], [13]⟩,
        ⟨3479, true, false, [744], [5, 13]⟩,
        ⟨3479, true, false, [744], [5, 13]⟩,
        ⟨3478, true, false, [744], [5, 13]⟩,
        ⟨3460, true, false, [744], [5, 13]⟩,
        ⟨1886, false, false, [744, 77193], []⟩,
        ⟨50, false, false, [744, 77193], []⟩,
        ⟨3480, false, false, [744], []⟩,
        ⟨3482, false, false, [744], []⟩,
        ⟨3483, true, false, [], [77191]⟩,
        ⟨3483, true, false, [], [77191]⟩,
        ⟨3462, false, true, [], [77191]⟩
      ]⟩,
    ⟨[747, 77583], [747, 77583], .contexts []⟩,
    ⟨[77327, 3], [747, 77583], .contexts [
        ⟨3467, false, false, [], []⟩,
        ⟨3470, false, false, [], []⟩,
        ⟨3485, false, false, [], []⟩,
        ⟨3485, false, false, [], []⟩
      ]⟩,
    ⟨[751], [499, 747], .source 440⟩,
    ⟨[77583, 13], [77583, 13], .contexts []⟩,
    ⟨[749], [746], .contexts [
        ⟨3471, false, false, [], []⟩
      ]⟩,
    ⟨[753], [749, 751], .source 441⟩,
    ⟨[77583, 13], [753, 77583], .contexts [
        ⟨3488, false, false, [], []⟩,
        ⟨3486, true, false, [746], [13]⟩,
        ⟨238, false, false, [746, 77327], []⟩,
        ⟨239, false, false, [746, 77327], []⟩,
        ⟨2653, false, false, [746], [3]⟩,
        ⟨3470, false, false, [746, 499], []⟩,
        ⟨3487, true, false, [746], [77583]⟩,
        ⟨3468, false, false, [746, 751], []⟩,
        ⟨3489, true, false, [], [751, 77583]⟩,
        ⟨3490, true, false, [], [77583]⟩
      ]⟩,
    ⟨[729, 77445], [729, 77445], .contexts []⟩,
    ⟨[77445, 15], [729, 77445], .contexts [
        ⟨3476, false, false, [], []⟩,
        ⟨3476, false, false, [], []⟩,
        ⟨2244, true, false, [], [15]⟩,
        ⟨3474, true, false, [726], [1, 15]⟩,
        ⟨2778, false, false, [726, 77447], []⟩,
        ⟨19, false, false, [726, 77447], []⟩,
        ⟨3475, false, false, [726], []⟩,
        ⟨3477, false, false, [726], []⟩,
        ⟨3428, true, false, [], [77445]⟩,
        ⟨3492, false, false, [], []⟩,
        ⟨3492, false, false, [], []⟩
      ]⟩,
    ⟨[77445, 11], [77443], .contexts [
        ⟨2325, false, false, [], []⟩,
        ⟨2326, false, false, [], []⟩,
        ⟨2239, false, false, [], []⟩,
        ⟨2239, false, false, [], []⟩
      ]⟩,
    ⟨[15, 11, 15], [10], .contexts [
        ⟨88, false, false, [], [10]⟩
      ]⟩,
    ⟨[77443, 15], [77443, 15], .contexts []⟩,
    ⟨[77443, 15], [727, 77443], .contexts [
        ⟨3496, false, false, [], []⟩,
        ⟨2240, true, false, [], [15]⟩,
        ⟨3493, true, false, [728], [11, 15]⟩,
        ⟨3495, false, false, [728, 77445], []⟩,
        ⟨91, false, false, [728, 77445], []⟩,
        ⟨3494, false, false, [728], []⟩,
        ⟨3454, true, false, [], [77443]⟩
      ]⟩,
    ⟨[743, 77191], [743, 77191], .contexts []⟩,
    ⟨[77191, 3], [77189], .contexts [
        ⟨659, false, false, [], []⟩,
        ⟨660, false, false, [], []⟩,
        ⟨546, false, false, [], []⟩,
        ⟨546, false, false, [], []⟩
      ]⟩,
    ⟨[77189], [77189], .contexts []⟩,
    ⟨[753, 77583], [753, 77583], .contexts []⟩,
    ⟨[77579, 15], [77579, 15], .contexts []⟩,
    ⟨[77579], [77579], .contexts []⟩,
    ⟨[755], [752], .source 442⟩,
    ⟨[755], [755], .contexts []⟩,
    ⟨[752], [752], .contexts []⟩,
    ⟨[755], [752], .contexts [
        ⟨3505, false, false, [], []⟩,
        ⟨3504, false, false, [], []⟩,
        ⟨3506, false, false, [], []⟩,
        ⟨3506, false, false, [], []⟩
      ]⟩,
    ⟨[77579, 15], [755, 77579], .contexts [
        ⟨3502, false, false, [], []⟩,
        ⟨3113, true, false, [], [15]⟩,
        ⟨3117, true, false, [], [13, 15]⟩,
        ⟨3501, true, false, [752], [15, 13, 15]⟩,
        ⟨3501, true, false, [752], [15, 13, 15]⟩,
        ⟨3491, true, false, [752], [15, 13, 15]⟩,
        ⟨3488, true, false, [752], [15, 13, 15]⟩,
        ⟨3449, false, false, [752, 77583], []⟩,
        ⟨149, false, false, [752, 77583], []⟩,
        ⟨3167, false, false, [752], [13]⟩,
        ⟨3168, false, false, [752], [13]⟩,
        ⟨3116, false, false, [752], [13]⟩,
        ⟨3116, false, false, [752], [13]⟩,
        ⟨3169, false, false, [752], []⟩,
        ⟨3170, false, false, [752], []⟩,
        ⟨3112, false, false, [752], []⟩,
        ⟨3112, false, false, [752], []⟩,
        ⟨3503, false, false, [752], []⟩,
        ⟨3507, true, false, [], [77579]⟩
      ]⟩,
    ⟨[727, 77443], [727, 77443], .contexts []⟩,
    ⟨[77443, 9], [77441], .contexts [
        ⟨2328, false, false, [], []⟩,
        ⟨2329, false, false, [], []⟩,
        ⟨2235, false, false, [], []⟩,
        ⟨2235, false, false, [], []⟩
      ]⟩,
    ⟨[77443, 8], [77443, 9], .contexts [
        ⟨77, false, false, [77443], []⟩
      ]⟩,
    ⟨[77441, 15], [77441, 15], .contexts []⟩,
    ⟨[77441], [77441], .contexts []⟩,
    ⟨[755, 77579], [755, 77579], .contexts []⟩,
    ⟨[77577, 15], [77577, 15], .contexts []⟩,
    ⟨[77577], [77577], .contexts []⟩,
    ⟨[753], [754], .contexts [
        ⟨3504, true, true, [], []⟩
      ]⟩,
    ⟨[754], [754], .contexts []⟩,
    ⟨[753], [754], .contexts [
        ⟨3517, false, false, [], []⟩,
        ⟨3518, false, false, [], []⟩,
        ⟨3518, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 055. -/
def y322TCContextRaw055 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[729, 77441], [729, 77441], .contexts []⟩,
    ⟨[77441, 15], [729, 77441], .contexts [
        ⟨3512, false, false, [], []⟩,
        ⟨3512, false, false, [], []⟩,
        ⟨2236, true, false, [], [15]⟩,
        ⟨3509, true, false, [726], [9, 15]⟩,
        ⟨3509, true, false, [726], [9, 15]⟩,
        ⟨3497, true, false, [726], [9, 15]⟩,
        ⟨3496, true, false, [726], [9, 15]⟩,
        ⟨2787, false, false, [726, 77443], []⟩,
        ⟨3511, false, false, [726], []⟩,
        ⟨3510, false, false, [726], []⟩,
        ⟨3513, false, false, [726], []⟩,
        ⟨3428, true, false, [], [77441]⟩,
        ⟨3520, false, false, [], []⟩,
        ⟨3520, false, false, [], []⟩
      ]⟩,
    ⟨[77439, 15], [77439, 15], .contexts []⟩,
    ⟨[77439], [77439], .contexts []⟩,
    ⟨[753, 77577], [753, 77577], .contexts []⟩,
    ⟨[77577, 15], [753, 77577], .contexts [
        ⟨3515, false, false, [], []⟩,
        ⟨3515, false, false, [], []⟩,
        ⟨3110, true, false, [], [15]⟩,
        ⟨3514, true, false, [754], [1, 15]⟩,
        ⟨3514, true, false, [754], [1, 15]⟩,
        ⟨3508, true, false, [754], [1, 15]⟩,
        ⟨3502, true, false, [754], [1, 15]⟩,
        ⟨2778, false, false, [754, 77579], []⟩,
        ⟨19, false, false, [754, 77579], []⟩,
        ⟨3172, false, false, [754], []⟩,
        ⟨3173, false, false, [754], []⟩,
        ⟨3109, false, false, [754], []⟩,
        ⟨3109, false, false, [754], []⟩,
        ⟨3516, false, false, [754], []⟩,
        ⟨3519, true, false, [], [77577]⟩,
        ⟨3524, false, false, [], []⟩,
        ⟨3524, false, false, [], []⟩
      ]⟩,
    ⟨[77577, 11], [77575], .contexts [
        ⟨3174, false, false, [], []⟩,
        ⟨3175, false, false, [], []⟩,
        ⟨3105, false, false, [], []⟩,
        ⟨3105, false, false, [], []⟩
      ]⟩,
    ⟨[77575, 15], [77575, 15], .contexts []⟩,
    ⟨[77575], [77575], .contexts []⟩,
    ⟨[727, 77439], [727, 77439], .contexts []⟩,
    ⟨[77439, 15, 5], [727, 77437], .contexts [
        ⟨3522, false, false, [], [5]⟩,
        ⟨3522, false, false, [], [5]⟩,
        ⟨2232, true, false, [], [15, 5]⟩,
        ⟨3521, true, false, [728], [1, 15, 5]⟩,
        ⟨2778, false, false, [728, 77441], [5]⟩,
        ⟨19, false, false, [728, 77441], [5]⟩,
        ⟨2330, false, false, [728], [5]⟩,
        ⟨2331, false, false, [728], [5]⟩,
        ⟨2231, false, false, [728], [5]⟩,
        ⟨2231, false, false, [728], [5]⟩,
        ⟨3523, false, false, [728], [5]⟩,
        ⟨3454, true, false, [], [77439, 5]⟩,
        ⟨3529, false, false, [], [5]⟩,
        ⟨3529, false, false, [], [5]⟩,
        ⟨2228, false, false, [727], []⟩
      ]⟩,
    ⟨[77439, 5], [77437], .contexts [
        ⟨2332, false, false, [], []⟩,
        ⟨2333, false, false, [], []⟩,
        ⟨2227, false, false, [], []⟩,
        ⟨2227, false, false, [], []⟩
      ]⟩,
    ⟨[15, 5, 15], [4], .contexts [
        ⟨47, false, false, [], [4]⟩
      ]⟩,
    ⟨[77439, 4], [77439, 5], .contexts [
        ⟨50, false, false, [77439], []⟩
      ]⟩,
    ⟨[77437, 15], [77437, 15], .contexts []⟩,
    ⟨[77437], [77437], .contexts []⟩,
    ⟨[755, 77575], [755, 77575], .contexts []⟩,
    ⟨[77575, 15, 9], [755, 77573], .contexts [
        ⟨3527, false, false, [], [9]⟩,
        ⟨3527, false, false, [], [9]⟩,
        ⟨3106, true, false, [], [15, 9]⟩,
        ⟨3525, true, false, [752], [11, 15, 9]⟩,
        ⟨3495, false, false, [752, 77577], [9]⟩,
        ⟨91, false, false, [752, 77577], [9]⟩,
        ⟨3526, false, false, [752], [9]⟩,
        ⟨3528, false, false, [752], [9]⟩,
        ⟨3507, true, false, [], [77575, 9]⟩,
        ⟨3536, false, false, [], [9]⟩,
        ⟨3536, false, false, [], [9]⟩,
        ⟨3102, false, false, [755], []⟩
      ]⟩,
    ⟨[77575, 9], [77573], .contexts [
        ⟨3176, false, false, [], []⟩,
        ⟨3177, false, false, [], []⟩,
        ⟨3101, false, false, [], []⟩,
        ⟨3101, false, false, [], []⟩
      ]⟩,
    ⟨[77573, 15], [77573, 15], .contexts []⟩,
    ⟨[77573], [77573], .contexts []⟩,
    ⟨[729, 77437], [729, 77437], .contexts []⟩,
    ⟨[729, 77435, 15], [77435], .contexts [
        ⟨2225, true, false, [729], [15]⟩,
        ⟨3541, true, false, [], [3, 15]⟩,
        ⟨3541, true, false, [], [3, 15]⟩,
        ⟨3428, false, false, [], [77437, 3, 15]⟩,
        ⟨3535, true, false, [726], [3, 15]⟩,
        ⟨3531, true, false, [726], [3, 15]⟩,
        ⟨3533, true, false, [726], [3, 15]⟩,
        ⟨3532, true, false, [726, 77439], [3, 15]⟩,
        ⟨3530, false, false, [726], [15, 3, 15]⟩,
        ⟨3534, true, false, [], [3, 15]⟩,
        ⟨3534, true, false, [], [3, 15]⟩,
        ⟨1893, false, false, [77437], []⟩,
        ⟨36, false, false, [77437], []⟩,
        ⟨2334, false, false, [], []⟩,
        ⟨2335, false, false, [], []⟩,
        ⟨2224, false, false, [], []⟩,
        ⟨2224, false, false, [], []⟩
      ]⟩,
    ⟨[77435, 15], [77435, 15], .contexts []⟩,
    ⟨[77435], [77435], .contexts []⟩,
    ⟨[753, 77573], [753, 77573], .contexts []⟩,
    ⟨[753, 77571, 15], [77571], .contexts [
        ⟨3099, true, false, [753], [15]⟩,
        ⟨3545, true, false, [], [1, 15]⟩,
        ⟨3545, true, false, [], [1, 15]⟩,
        ⟨3519, false, false, [], [77573, 1, 15]⟩,
        ⟨3540, true, false, [754], [1, 15]⟩,
        ⟨3538, true, false, [754], [1, 15]⟩,
        ⟨77, true, false, [754, 77575], [1, 15]⟩,
        ⟨2787, true, false, [754, 77575], [1, 15]⟩,
        ⟨3537, false, false, [754], [15, 1, 15]⟩,
        ⟨3539, true, false, [], [1, 15]⟩,
        ⟨3539, true, false, [], [1, 15]⟩,
        ⟨2778, false, false, [77573], []⟩,
        ⟨19, false, false, [77573], []⟩,
        ⟨3178, false, false, [], []⟩,
        ⟨3179, false, false, [], []⟩,
        ⟨3098, false, false, [], []⟩,
        ⟨3098, false, false, [], []⟩
      ]⟩,
    ⟨[77571, 15], [77571, 15], .contexts []⟩,
    ⟨[77571], [77571], .contexts []⟩,
    ⟨[727, 77435], [727, 77435], .contexts []⟩,
    ⟨[727, 77431], [727, 77431], .contexts []⟩,
    ⟨[727, 77431], [727, 77431], .contexts []⟩,
    ⟨[727, 77431, 1], [77435], .contexts [
        ⟨3551, true, false, [], [1]⟩,
        ⟨3550, true, false, [], [1]⟩,
        ⟨2219, true, false, [727], [1]⟩,
        ⟨2222, true, false, [727], [15, 1]⟩,
        ⟨3549, true, false, [], [1, 15, 1]⟩,
        ⟨3549, true, false, [], [1, 15, 1]⟩,
        ⟨3454, false, false, [], [77435, 1, 15, 1]⟩,
        ⟨3544, true, false, [728], [1, 15, 1]⟩,
        ⟨3542, true, false, [728], [1, 15, 1]⟩,
        ⟨3543, true, false, [], [1, 15, 1]⟩,
        ⟨3543, true, false, [], [1, 15, 1]⟩,
        ⟨911, false, false, [77435], []⟩
      ]⟩,
    ⟨[77431, 1], [729, 77435], .contexts [
        ⟨3552, false, false, [726], []⟩,
        ⟨3544, false, false, [726], []⟩,
        ⟨3428, true, false, [], [77435]⟩
      ]⟩,
    ⟨[77435, 1], [77433], .contexts [
        ⟨2336, false, false, [], []⟩
      ]⟩,
    ⟨[755, 77571], [755, 77571], .contexts []⟩,
    ⟨[77571, 5], [77569], .contexts [
        ⟨3180, false, false, [], []⟩,
        ⟨3181, false, false, [], []⟩,
        ⟨3095, false, false, [], []⟩,
        ⟨3095, false, false, [], []⟩
      ]⟩,
    ⟨[77571, 4], [77571, 5], .contexts [
        ⟨50, false, false, [77571], []⟩
      ]⟩,
    ⟨[77569, 15], [77569, 15], .contexts []⟩,
    ⟨[77569], [77569], .contexts []⟩,
    ⟨[77569, 15], [753, 77569], .contexts [
        ⟨3558, false, false, [], []⟩,
        ⟨3096, true, false, [], [15]⟩,
        ⟨3555, true, false, [754], [5, 15]⟩,
        ⟨3555, true, false, [754], [5, 15]⟩,
        ⟨3507, false, false, [754], [77571, 5, 15]⟩,
        ⟨3548, true, false, [754, 752], [5, 15]⟩,
        ⟨3546, true, false, [754, 752], [5, 15]⟩,
        ⟨3547, true, false, [754], [5, 15]⟩,
        ⟨3547, true, false, [754], [5, 15]⟩,
        ⟨3532, false, false, [754, 77571], []⟩,
        ⟨3557, false, false, [754], []⟩,
        ⟨3556, false, false, [754], []⟩,
        ⟨3559, false, false, [754], []⟩,
        ⟨3519, true, false, [], [77569]⟩
      ]⟩,
    ⟨[753, 77569], [753, 77569], .contexts []⟩,
    ⟨[753, 77567], [753, 77567], .contexts []⟩,
    ⟨[753, 77567], [753, 77567], .contexts []⟩,
    ⟨[77569, 3], [77567], .contexts [
        ⟨3183, false, false, [], []⟩,
        ⟨3184, false, false, [], []⟩,
        ⟨3091, false, false, [], []⟩,
        ⟨3091, false, false, [], []⟩
      ]⟩,
    ⟨[77569, 2], [77569, 3], .contexts [
        ⟨36, false, false, [77569], []⟩
      ]⟩,
    ⟨[77567, 15], [77567, 15], .contexts []⟩,
    ⟨[77567], [77567], .contexts []⟩,
    ⟨[77567, 15], [755, 77567], .contexts [
        ⟨3566, false, false, [], []⟩,
        ⟨3563, true, false, [752], [15]⟩,
        ⟨3562, true, false, [752], [15]⟩,
        ⟨3092, true, false, [], [15]⟩,
        ⟨3561, true, false, [752], [3, 15]⟩,
        ⟨3561, true, false, [752], [3, 15]⟩,
        ⟨3560, true, false, [752], [3, 15]⟩,
        ⟨3558, true, false, [752], [3, 15]⟩,
        ⟨1893, false, false, [752, 77569], []⟩,
        ⟨3565, false, false, [752], []⟩,
        ⟨3564, false, false, [752], []⟩,
        ⟨3567, false, false, [752], []⟩,
        ⟨3507, true, false, [], [77567]⟩
      ]⟩,
    ⟨[755, 77567], [755, 77567], .contexts []⟩,
    ⟨[755, 77563], [755, 77563], .contexts []⟩,
    ⟨[755, 77563], [755, 77563], .contexts []⟩,
    ⟨[77563, 1], [77563, 1], .contexts []⟩,
    ⟨[77563, 1], [753, 77567], .contexts [
        ⟨3572, false, false, [], []⟩,
        ⟨3571, true, false, [754], [1]⟩,
        ⟨3570, true, false, [754], [1]⟩,
        ⟨3085, true, false, [], [1]⟩,
        ⟨3088, true, false, [], [15, 1]⟩,
        ⟨3569, true, false, [754], [1, 15, 1]⟩,
        ⟨3569, true, false, [754], [1, 15, 1]⟩,
        ⟨3568, true, false, [754], [1, 15, 1]⟩,
        ⟨3566, true, false, [754], [1, 15, 1]⟩,
        ⟨911, false, false, [754, 77567], []⟩,
        ⟨3567, false, false, [754], []⟩,
        ⟨3519, true, false, [], [77567]⟩
      ]⟩,
    ⟨[77567, 1], [77565], .contexts [
        ⟨3185, false, false, [], []⟩
      ]⟩,
    ⟨[77605], [77113, 7], .source 38867⟩,
    ⟨[77113, 7], [77605], .contexts [
        ⟨3575, true, false, [], []⟩
      ]⟩,
    ⟨[77605], [77605], .contexts []⟩,
    ⟨[77605], [77605], .contexts []⟩,
    ⟨[77113, 7], [77605], .contexts [
        ⟨3576, false, false, [], []⟩,
        ⟨3577, false, false, [], []⟩,
        ⟨3578, false, false, [], []⟩,
        ⟨3578, false, false, [], []⟩
      ]⟩,
    ⟨[77113, 1, 7], [77483], .contexts [
        ⟨379, false, false, [], [7]⟩,
        ⟨1118, false, false, [], [77111, 7]⟩,
        ⟨337, true, false, [], [7]⟩,
        ⟨331, true, false, [], [7]⟩,
        ⟨331, true, false, [], [7]⟩,
        ⟨330, true, false, [], [7]⟩,
        ⟨329, true, false, [], [7]⟩,
        ⟨299, true, false, [], [11, 7]⟩,
        ⟨299, true, false, [], [11, 7]⟩,
        ⟨298, true, false, [], [11, 7]⟩,
        ⟨1812, true, false, [], [11, 7]⟩,
        ⟨1811, true, false, [], [11, 7]⟩,
        ⟨1089, true, false, [77359], [7]⟩,
        ⟨1088, true, false, [77359], [7]⟩,
        ⟨2666, false, false, [], [7, 7]⟩,
        ⟨62, false, false, [77483], []⟩,
        ⟨2665, false, false, [], []⟩,
        ⟨2664, false, false, [], []⟩,
        ⟨2665, false, false, [], []⟩,
        ⟨2665, false, false, [], []⟩
      ]⟩,
    ⟨[77605, 1], [77605, 1], .contexts []⟩,
    ⟨[77605, 1], [77483], .contexts [
        ⟨3581, false, false, [], []⟩,
        ⟨3579, true, false, [], [1]⟩,
        ⟨1764, false, false, [77113], []⟩,
        ⟨1765, false, false, [77113], []⟩,
        ⟨3580, false, false, [], []⟩,
        ⟨2667, false, false, [], []⟩,
        ⟨1118, true, false, [], [77483]⟩
      ]⟩,
    ⟨[77483, 1], [77605], .contexts [
        ⟨3582, true, false, [], [1]⟩,
        ⟨18, false, false, [77605], []⟩,
        ⟨3578, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 056. -/
def y322TCContextRaw056 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93, 77361], [93, 77361], .contexts []⟩,
    ⟨[757], [93, 97], .source 443⟩,
    ⟨[77113, 5, 7, 5], [757, 77361, 5], .contexts [
        ⟨1829, true, false, [110], [5, 7, 5]⟩,
        ⟨49, false, false, [110, 77361], [7, 5]⟩,
        ⟨846, true, false, [], [77361, 7, 5]⟩,
        ⟨3584, false, false, [], [7, 5]⟩,
        ⟨3584, false, false, [], [7, 5]⟩,
        ⟨1823, true, false, [93], [7, 5]⟩,
        ⟨173, false, false, [93, 77235], [5]⟩,
        ⟨174, false, false, [93, 77235], [5]⟩,
        ⟨1109, false, false, [93], [1, 5]⟩,
        ⟨1110, false, false, [93], [1, 5]⟩,
        ⟨1111, false, false, [93, 97], [1, 5]⟩,
        ⟨865, true, false, [93], [77235, 1, 5]⟩,
        ⟨1107, false, false, [93], [1, 5]⟩,
        ⟨1108, false, false, [93], [1, 5]⟩,
        ⟨1108, false, false, [93], [1, 5]⟩,
        ⟨1820, false, false, [93, 97], [5]⟩,
        ⟨1827, false, false, [93, 97], [5]⟩,
        ⟨865, true, false, [93], [77361, 5]⟩,
        ⟨3585, true, false, [], [77361, 5]⟩
      ]⟩,
    ⟨[759], [757, 111], .source 444⟩,
    ⟨[759, 77605], [759, 77605], .contexts []⟩,
    ⟨[759, 77605], [759, 77605], .contexts []⟩,
    ⟨[77605, 5], [77605, 5], .contexts []⟩,
    ⟨[77605], [77605], .contexts []⟩,
    ⟨[759], [759], .contexts [
        ⟨24, false, false, [], [759]⟩
      ]⟩,
    ⟨[77605, 5], [759, 77605], .contexts [
        ⟨3590, false, false, [], []⟩,
        ⟨3579, true, false, [], [5]⟩,
        ⟨1776, false, false, [77113], []⟩,
        ⟨1777, false, false, [77113], []⟩,
        ⟨3586, false, false, [], [7]⟩,
        ⟨1829, false, false, [757], [7]⟩,
        ⟨3587, true, false, [], [77113, 7]⟩,
        ⟨3576, false, false, [759], []⟩,
        ⟨3588, false, false, [], []⟩,
        ⟨3589, false, false, [], []⟩,
        ⟨3591, false, false, [759], []⟩,
        ⟨3592, true, false, [], [77605]⟩
      ]⟩,
    ⟨[211, 77479], [211, 77479], .contexts []⟩,
    ⟨[211, 77479], [211, 77479], .contexts []⟩,
    ⟨[77605, 11], [77605, 11], .contexts []⟩,
    ⟨[211, 77479], [211, 77479], .contexts [
        ⟨2573, false, false, [211], []⟩
      ]⟩,
    ⟨[211], [211], .contexts [
        ⟨24, false, false, [], [211]⟩
      ]⟩,
    ⟨[211, 77479], [211, 77479], .contexts [
        ⟨3598, true, false, [], [77479]⟩
      ]⟩,
    ⟨[77605, 11], [211, 77479], .contexts [
        ⟨3596, false, false, [], []⟩,
        ⟨3579, true, false, [], [11]⟩,
        ⟨1781, false, false, [77113], []⟩,
        ⟨1782, false, false, [77113], []⟩,
        ⟨1526, false, false, [], [7]⟩,
        ⟨1513, false, false, [], [7]⟩,
        ⟨1514, false, false, [], [7]⟩,
        ⟨1514, false, false, [], [7]⟩,
        ⟨2566, false, false, [211], []⟩,
        ⟨3594, false, false, [], []⟩,
        ⟨3595, false, false, [], []⟩,
        ⟨3597, false, false, [], []⟩,
        ⟨3599, false, false, [], []⟩
      ]⟩,
    ⟨[77479, 11], [209, 77605], .contexts [
        ⟨3600, true, false, [210], [11]⟩,
        ⟨90, false, false, [210, 77605], []⟩,
        ⟨1492, true, false, [], [77605]⟩
      ]⟩,
    ⟨[13, 77605], [13, 77605], .contexts []⟩,
    ⟨[13, 77605], [13, 77605], .contexts []⟩,
    ⟨[77605, 15], [13, 77605], .contexts [
        ⟨3579, true, false, [], [15]⟩,
        ⟨1791, false, false, [77113], []⟩,
        ⟨1792, false, false, [77113], []⟩,
        ⟨1150, false, false, [], [7]⟩,
        ⟨3576, false, false, [13], []⟩,
        ⟨3602, false, false, [], []⟩,
        ⟨3603, false, false, [], []⟩,
        ⟨3591, false, false, [13], []⟩,
        ⟨153, true, false, [], [77605]⟩
      ]⟩,
    ⟨[77607], [77465, 15], .source 38868⟩,
    ⟨[77465, 15], [77607], .contexts [
        ⟨3605, true, false, [], []⟩
      ]⟩,
    ⟨[77607, 15], [77465], .contexts [
        ⟨3606, true, false, [], [15]⟩,
        ⟨3, false, false, [77465], []⟩,
        ⟨2278, false, false, [], []⟩
      ]⟩,
    ⟨[77607], [77607], .contexts []⟩,
    ⟨[77607], [77607], .contexts []⟩,
    ⟨[77465, 15], [77607], .contexts [
        ⟨3606, false, false, [], []⟩,
        ⟨3608, false, false, [], []⟩,
        ⟨3609, false, false, [], []⟩,
        ⟨3609, false, false, [], []⟩
      ]⟩,
    ⟨[433, 77465], [433, 77465], .contexts []⟩,
    ⟨[433, 77465], [433, 77465], .contexts []⟩,
    ⟨[433, 77607], [433, 77607], .contexts []⟩,
    ⟨[433, 77607], [433, 77607], .contexts []⟩,
    ⟨[433, 77607], [433, 77607], .contexts []⟩,
    ⟨[77607], [77607], .contexts []⟩,
    ⟨[433], [433], .contexts [
        ⟨24, false, false, [], [433]⟩
      ]⟩,
    ⟨[77607, 3], [433, 77607], .contexts [
        ⟨3610, true, false, [], [3]⟩,
        ⟨34, false, false, [77465], []⟩,
        ⟨37, false, false, [77465], []⟩,
        ⟨2523, false, false, [], [15]⟩,
        ⟨2525, false, false, [], [15]⟩,
        ⟨3611, false, false, [], [15]⟩,
        ⟨3612, false, false, [], [15]⟩,
        ⟨3612, false, false, [], [15]⟩,
        ⟨3606, false, false, [433], []⟩,
        ⟨3613, false, false, [], []⟩,
        ⟨3614, false, false, [], []⟩,
        ⟨3615, false, false, [], []⟩,
        ⟨3616, false, false, [433], []⟩,
        ⟨3617, true, false, [], [77607]⟩
      ]⟩,
    ⟨[463, 77607], [463, 77607], .contexts []⟩,
    ⟨[463, 77607], [463, 77607], .contexts []⟩,
    ⟨[77607, 5], [77607, 5], .contexts []⟩,
    ⟨[463], [463], .contexts [
        ⟨24, false, false, [], [463]⟩
      ]⟩,
    ⟨[77607, 5], [463, 77607], .contexts [
        ⟨3621, false, false, [], []⟩,
        ⟨3610, true, false, [], [5]⟩,
        ⟨48, false, false, [77465], []⟩,
        ⟨51, false, false, [77465], []⟩,
        ⟨2535, false, false, [], [15]⟩,
        ⟨3606, false, false, [463], []⟩,
        ⟨3619, false, false, [], []⟩,
        ⟨3620, false, false, [], []⟩,
        ⟨3616, false, false, [463], []⟩,
        ⟨3622, true, false, [], [77607]⟩
      ]⟩,
    ⟨[461, 77607], [461, 77607], .contexts []⟩,
    ⟨[461, 77607], [461, 77607], .contexts []⟩,
    ⟨[77607, 11], [77607, 11], .contexts []⟩,
    ⟨[77607, 13], [439, 77607], .contexts [
        ⟨3610, true, false, [], [13]⟩,
        ⟨408, false, false, [77465], []⟩,
        ⟨410, false, false, [77465], []⟩,
        ⟨2277, false, false, [], [15, 13, 15]⟩,
        ⟨2304, false, false, [], [15, 13, 15]⟩,
        ⟨2282, false, false, [], [15, 13, 15]⟩,
        ⟨2282, false, false, [], [15, 13, 15]⟩,
        ⟨2281, false, false, [], [13, 15]⟩,
        ⟨2509, false, false, [], [13, 15]⟩,
        ⟨2496, false, false, [], [13, 15]⟩,
        ⟨2496, false, false, [], [13, 15]⟩,
        ⟨3333, false, false, [], [15]⟩,
        ⟨3334, false, false, [], [15]⟩,
        ⟨3335, false, false, [], [15]⟩,
        ⟨3336, false, false, [], [15]⟩,
        ⟨3606, false, false, [439], []⟩,
        ⟨3616, false, false, [439], []⟩
      ]⟩,
    ⟨[439], [439], .contexts [
        ⟨24, false, false, [], [439]⟩,
        ⟨2500, false, false, [], []⟩,
        ⟨2501, false, false, [], []⟩
      ]⟩,
    ⟨[77609], [77607, 1], .source 38869⟩,
    ⟨[77607, 1], [77609], .contexts [
        ⟨3629, true, false, [], []⟩
      ]⟩,
    ⟨[77609, 1], [77607], .contexts [
        ⟨3630, true, false, [], [1]⟩,
        ⟨18, false, false, [77607], []⟩,
        ⟨3609, false, false, [], []⟩
      ]⟩,
    ⟨[77609], [77609], .contexts []⟩,
    ⟨[77609], [77609], .contexts []⟩,
    ⟨[77607, 1], [77609], .contexts [
        ⟨3630, false, false, [], []⟩,
        ⟨3632, false, false, [], []⟩,
        ⟨3633, false, false, [], []⟩,
        ⟨3633, false, false, [], []⟩
      ]⟩,
    ⟨[463, 77609], [463, 77609], .contexts []⟩,
    ⟨[463, 77609], [463, 77609], .contexts []⟩,
    ⟨[77609], [77609], .contexts []⟩,
    ⟨[461, 77609], [461, 77609], .contexts []⟩,
    ⟨[461, 77609], [461, 77609], .contexts []⟩,
    ⟨[77609, 11], [77609, 11], .contexts []⟩,
    ⟨[77609, 11], [461, 77609], .contexts [
        ⟨3640, false, false, [], []⟩,
        ⟨3634, true, false, [], [11]⟩,
        ⟨181, false, false, [77607], []⟩,
        ⟨182, false, false, [77607], []⟩,
        ⟨3626, false, false, [], [1]⟩,
        ⟨3626, false, false, [], [1]⟩,
        ⟨3610, true, false, [], [11, 1]⟩,
        ⟨89, false, false, [77465], [1]⟩,
        ⟨92, false, false, [77465], [1]⟩,
        ⟨2540, false, false, [], [15, 1]⟩,
        ⟨3606, false, false, [461], [1]⟩,
        ⟨3624, false, false, [], [1]⟩,
        ⟨3625, false, false, [], [1]⟩,
        ⟨3616, false, false, [461], [1]⟩,
        ⟨2533, true, false, [], [77607, 1]⟩,
        ⟨3624, false, false, [], [1]⟩,
        ⟨3625, false, false, [], [1]⟩,
        ⟨3625, false, false, [], [1]⟩,
        ⟨3630, false, false, [461], []⟩,
        ⟨3638, false, false, [], []⟩,
        ⟨3639, false, false, [], []⟩
      ]⟩,
    ⟨[77609, 15], [77609, 15], .contexts []⟩,
    ⟨[77609, 15], [461, 77461], .contexts [
        ⟨3642, false, false, [], []⟩,
        ⟨3634, true, false, [], [15]⟩,
        ⟨199, false, false, [77607], []⟩,
        ⟨200, false, false, [77607], []⟩,
        ⟨3607, false, false, [], [1]⟩,
        ⟨2306, false, false, [], [1]⟩,
        ⟨2278, false, false, [], [1]⟩,
        ⟨2278, false, false, [], [1]⟩,
        ⟨2307, false, false, [], []⟩,
        ⟨2730, false, false, [], []⟩,
        ⟨2542, false, false, [], []⟩,
        ⟨2542, false, false, [], []⟩,
        ⟨2732, false, false, [461], []⟩,
        ⟨2533, true, false, [], [77461]⟩
      ]⟩,
    ⟨[761], [461, 685], .source 445⟩,
    ⟨[763], [761, 665], .source 446⟩,
    ⟨[763, 77495], [763, 77495], .contexts []⟩,
    ⟨[763, 77495], [763, 77495], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 057. -/
def y322TCContextRaw057 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77609, 15, 13, 15, 13, 15], [763, 77495], .contexts [
        ⟨3642, false, false, [], [13, 15, 13, 15]⟩,
        ⟨3643, false, false, [], [13, 15, 13, 15]⟩,
        ⟨2541, false, false, [], [13, 15, 13, 15]⟩,
        ⟨2542, false, false, [], [13, 15, 13, 15]⟩,
        ⟨2542, false, false, [], [13, 15, 13, 15]⟩,
        ⟨3343, false, false, [461], [15, 13, 15]⟩,
        ⟨3644, true, false, [], [77601, 15, 13, 15]⟩,
        ⟨3147, false, false, [761], [13, 15]⟩,
        ⟨3313, false, false, [761], [13, 15]⟩,
        ⟨3645, true, false, [], [77491, 13, 15]⟩,
        ⟨2907, false, false, [763], [15]⟩,
        ⟨2954, false, false, [763], []⟩,
        ⟨3646, false, false, [], []⟩,
        ⟨3647, false, false, [], []⟩
      ]⟩,
    ⟨[15, 13, 15, 13, 15, 13], [], .contexts [
        ⟨407, false, false, [], []⟩
      ]⟩,
    ⟨[77495, 13], [77495, 13], .contexts []⟩,
    ⟨[765], [762], .source 447⟩,
    ⟨[762], [762], .contexts []⟩,
    ⟨[77495, 13], [765, 77609], .contexts [
        ⟨3650, false, false, [], []⟩,
        ⟨3648, true, false, [762], [13]⟩,
        ⟨3649, false, false, [762, 77609], []⟩,
        ⟨3637, false, false, [762], []⟩,
        ⟨3652, true, false, [], [77609]⟩,
        ⟨3652, true, false, [], [77609]⟩,
        ⟨3651, true, false, [], [77609]⟩
      ]⟩,
    ⟨[763], [764], .contexts [
        ⟨3651, true, true, [], []⟩
      ]⟩,
    ⟨[77609, 13], [763, 77495], .contexts [
        ⟨3653, true, false, [764], [13]⟩,
        ⟨98, false, false, [764, 77495], []⟩,
        ⟨3654, true, false, [], [77495]⟩
      ]⟩,
    ⟨[77611], [77609, 3], .source 38870⟩,
    ⟨[77609, 3], [77611], .contexts [
        ⟨3656, true, false, [], []⟩
      ]⟩,
    ⟨[77611, 3], [77609], .contexts [
        ⟨3657, true, false, [], [3]⟩,
        ⟨35, false, false, [77609], []⟩,
        ⟨3633, false, false, [], []⟩
      ]⟩,
    ⟨[77611], [77611], .contexts []⟩,
    ⟨[77609, 3], [77611], .contexts [
        ⟨3657, false, false, [], []⟩,
        ⟨3659, false, false, [], []⟩,
        ⟨3659, false, false, [], []⟩
      ]⟩,
    ⟨[433, 77609], [433, 77609], .contexts []⟩,
    ⟨[433, 77609], [433, 77609], .contexts []⟩,
    ⟨[433, 77609], [433, 77609], .contexts []⟩,
    ⟨[433, 77611], [433, 77611], .contexts []⟩,
    ⟨[433, 77611], [433, 77611], .contexts []⟩,
    ⟨[433, 77611], [433, 77611], .contexts []⟩,
    ⟨[77611, 1], [77611, 1], .contexts []⟩,
    ⟨[77611], [77611], .contexts []⟩,
    ⟨[77611, 1], [433, 77611], .contexts [
        ⟨3667, false, false, [], []⟩,
        ⟨3660, true, false, [], [1]⟩,
        ⟨213, false, false, [77609], []⟩,
        ⟨216, false, false, [77609], []⟩,
        ⟨3631, false, false, [], [3, 1, 3]⟩,
        ⟨3608, false, false, [], [3, 1, 3]⟩,
        ⟨3609, false, false, [], [3, 1, 3]⟩,
        ⟨3609, false, false, [], [3, 1, 3]⟩,
        ⟨3618, false, false, [], [1, 3]⟩,
        ⟨3613, false, false, [], [1, 3]⟩,
        ⟨3615, false, false, [], [1, 3]⟩,
        ⟨3615, false, false, [], [1, 3]⟩,
        ⟨3630, false, false, [433], [3]⟩,
        ⟨3661, false, false, [], [3]⟩,
        ⟨3662, false, false, [], [3]⟩,
        ⟨3663, false, false, [], [3]⟩,
        ⟨3657, false, false, [433], []⟩,
        ⟨3664, false, false, [], []⟩,
        ⟨3665, false, false, [], []⟩,
        ⟨3666, false, false, [], []⟩,
        ⟨3668, false, false, [433], []⟩
      ]⟩,
    ⟨[77611, 1], [433, 77611], .contexts [
        ⟨3669, false, false, [], []⟩,
        ⟨3617, true, false, [], [77611]⟩
      ]⟩,
    ⟨[461, 77611], [461, 77611], .contexts []⟩,
    ⟨[461, 77611], [461, 77611], .contexts []⟩,
    ⟨[77611, 11], [77611, 11], .contexts []⟩,
    ⟨[763, 77497], [763, 77497], .contexts []⟩,
    ⟨[763, 77497], [763, 77497], .contexts []⟩,
    ⟨[77611, 13], [77611, 13], .contexts []⟩,
    ⟨[763], [763], .contexts [
        ⟨24, false, false, [], [763]⟩
      ]⟩,
    ⟨[77611, 13], [763, 77497], .contexts [
        ⟨3676, false, false, [], []⟩,
        ⟨3660, true, false, [], [13]⟩,
        ⟨238, false, false, [77609], []⟩,
        ⟨239, false, false, [77609], []⟩,
        ⟨3655, false, false, [], [3]⟩,
        ⟨3646, false, false, [], [3]⟩,
        ⟨3647, false, false, [], [3]⟩,
        ⟨3647, false, false, [], [3]⟩,
        ⟨2969, false, false, [763], []⟩,
        ⟨3674, false, false, [], []⟩,
        ⟨3675, false, false, [], []⟩,
        ⟨2977, false, false, [763], []⟩,
        ⟨3677, true, false, [], [77497]⟩
      ]⟩,
    ⟨[77497, 13], [765, 77611], .contexts [
        ⟨3678, true, false, [762], [13]⟩,
        ⟨98, false, false, [762, 77611], []⟩,
        ⟨3651, true, false, [], [77611]⟩
      ]⟩,
    ⟨[77613], [77611, 5], .source 38871⟩,
    ⟨[77611, 5], [77613], .contexts [
        ⟨3680, true, false, [], []⟩
      ]⟩,
    ⟨[77613, 5], [77611], .contexts [
        ⟨3681, true, false, [], [5]⟩,
        ⟨49, false, false, [77611], []⟩,
        ⟨3659, false, false, [], []⟩
      ]⟩,
    ⟨[77613], [77613], .contexts []⟩,
    ⟨[77613], [77613], .contexts []⟩,
    ⟨[77611, 5], [77613], .contexts [
        ⟨3681, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩,
        ⟨3684, false, false, [], []⟩,
        ⟨3684, false, false, [], []⟩
      ]⟩,
    ⟨[433, 77613], [433, 77613], .contexts []⟩,
    ⟨[433, 77613], [433, 77613], .contexts []⟩,
    ⟨[77613, 1], [77613, 1], .contexts []⟩,
    ⟨[77613], [77613], .contexts []⟩,
    ⟨[77613, 1], [433, 77613], .contexts [
        ⟨3688, false, false, [], []⟩,
        ⟨3685, true, false, [], [1]⟩,
        ⟨256, false, false, [77611], []⟩,
        ⟨257, false, false, [77611], []⟩,
        ⟨3667, false, false, [], [5]⟩,
        ⟨3670, false, false, [], [5]⟩,
        ⟨3664, false, false, [], [5]⟩,
        ⟨3666, false, false, [], [5]⟩,
        ⟨3666, false, false, [], [5]⟩,
        ⟨3681, false, false, [433], []⟩,
        ⟨3686, false, false, [], []⟩,
        ⟨3687, false, false, [], []⟩,
        ⟨3689, false, false, [433], []⟩,
        ⟨3617, true, false, [], [77613]⟩
      ]⟩,
    ⟨[77611, 3, 5, 3], [463, 77611], .contexts [
        ⟨3658, false, false, [], [5, 3]⟩,
        ⟨3632, false, false, [], [5, 3]⟩,
        ⟨3633, false, false, [], [5, 3]⟩,
        ⟨3633, false, false, [], [5, 3]⟩,
        ⟨3634, true, false, [], [5, 3]⟩,
        ⟨165, false, false, [77607], [3]⟩,
        ⟨166, false, false, [77607], [3]⟩,
        ⟨3621, false, false, [], [1, 3]⟩,
        ⟨3623, false, false, [], [1, 3]⟩,
        ⟨3619, false, false, [], [1, 3]⟩,
        ⟨3620, false, false, [], [1, 3]⟩,
        ⟨3620, false, false, [], [1, 3]⟩,
        ⟨3630, false, false, [463], [3]⟩,
        ⟨3635, false, false, [], [3]⟩,
        ⟨3636, false, false, [], [3]⟩,
        ⟨3637, false, false, [463], [3]⟩,
        ⟨3622, true, false, [], [77609, 3]⟩,
        ⟨3635, false, false, [], [3]⟩,
        ⟨3636, false, false, [], [3]⟩,
        ⟨3636, false, false, [], [3]⟩,
        ⟨3657, false, false, [463], []⟩
      ]⟩,
    ⟨[463, 77613], [463, 77613], .contexts []⟩,
    ⟨[463, 77613], [463, 77613], .contexts []⟩,
    ⟨[77613, 3], [77613, 3], .contexts []⟩,
    ⟨[77613, 3], [463, 77613], .contexts [
        ⟨3694, false, false, [], []⟩,
        ⟨3685, true, false, [], [3]⟩,
        ⟨264, false, false, [77611], []⟩,
        ⟨267, false, false, [77611], []⟩,
        ⟨3691, false, false, [], [5]⟩,
        ⟨3681, false, false, [463], []⟩,
        ⟨3692, false, false, [], []⟩,
        ⟨3693, false, false, [], []⟩,
        ⟨3689, false, false, [463], []⟩,
        ⟨3622, true, false, [], [77613]⟩
      ]⟩,
    ⟨[77611, 11, 5], [461, 77611, 5], .contexts [
        ⟨3673, false, false, [], [5]⟩,
        ⟨3673, false, false, [], [5]⟩,
        ⟨3660, true, false, [], [11, 5]⟩,
        ⟨231, false, false, [77609], [5]⟩,
        ⟨232, false, false, [77609], [5]⟩,
        ⟨3640, false, false, [], [3, 5]⟩,
        ⟨3641, false, false, [], [3, 5]⟩,
        ⟨3637, false, false, [461], [3, 5]⟩,
        ⟨2533, true, false, [], [77609, 3, 5]⟩,
        ⟨3638, false, false, [], [3, 5]⟩,
        ⟨3639, false, false, [], [3, 5]⟩,
        ⟨3639, false, false, [], [3, 5]⟩,
        ⟨3657, false, false, [461], [5]⟩,
        ⟨3671, false, false, [], [5]⟩,
        ⟨3672, false, false, [], [5]⟩,
        ⟨3668, false, false, [461], [5]⟩,
        ⟨2533, true, false, [], [77611, 5]⟩,
        ⟨3671, false, false, [], [5]⟩,
        ⟨3672, false, false, [], [5]⟩,
        ⟨3672, false, false, [], [5]⟩
      ]⟩,
    ⟨[763, 77499], [763, 77499], .contexts []⟩,
    ⟨[763, 77499], [763, 77499], .contexts []⟩,
    ⟨[77613, 13], [77613, 13], .contexts []⟩,
    ⟨[77613, 13], [763, 77499], .contexts [
        ⟨3699, false, false, [], []⟩,
        ⟨3685, true, false, [], [13]⟩,
        ⟨283, false, false, [77611], []⟩,
        ⟨284, false, false, [77611], []⟩,
        ⟨3676, false, false, [], [5]⟩,
        ⟨3678, false, false, [], [5]⟩,
        ⟨3674, false, false, [], [5]⟩,
        ⟨3675, false, false, [], [5]⟩,
        ⟨3675, false, false, [], [5]⟩,
        ⟨2981, false, false, [763], []⟩,
        ⟨3697, false, false, [], []⟩,
        ⟨3698, false, false, [], []⟩,
        ⟨2986, false, false, [763], []⟩,
        ⟨3677, true, false, [], [77499]⟩
      ]⟩,
    ⟨[77499, 13], [765, 77613], .contexts [
        ⟨3700, true, false, [762], [13]⟩,
        ⟨98, false, false, [762, 77613], []⟩,
        ⟨3651, true, false, [], [77613]⟩
      ]⟩,
    ⟨[77613, 1], [433, 77613], .contexts [
        ⟨3690, false, false, [], []⟩
      ]⟩,
    ⟨[767], [433, 763], .source 448⟩,
    ⟨[77501, 13], [77501, 13], .contexts []⟩,
    ⟨[769], [766], .source 449⟩,
    ⟨[771], [769, 763], .source 450⟩,
    ⟨[77501, 13], [771, 77501], .contexts [
        ⟨3704, false, false, [], []⟩,
        ⟨2989, true, false, [], [13]⟩,
        ⟨3703, false, false, [766], [77499, 1, 13]⟩,
        ⟨3700, true, false, [766, 433], [1, 13]⟩,
        ⟨3687, true, false, [766], [13, 1, 13]⟩,
        ⟨3687, true, false, [766], [13, 1, 13]⟩,
        ⟨3686, true, false, [766], [13, 1, 13]⟩,
        ⟨3702, true, false, [766], [13, 1, 13]⟩,
        ⟨3688, true, false, [766], [13, 1, 13]⟩,
        ⟨1587, false, false, [766, 77613], []⟩,
        ⟨190, false, false, [766, 77613], []⟩,
        ⟨3699, false, false, [766], [1]⟩,
        ⟨3700, false, false, [766], [1]⟩,
        ⟨3697, false, false, [766], [1]⟩,
        ⟨3698, false, false, [766], [1]⟩,
        ⟨3698, false, false, [766], [1]⟩,
        ⟨2989, false, false, [766, 763], []⟩,
        ⟨3705, true, false, [], [763, 77501]⟩,
        ⟨3706, true, false, [], [77501]⟩
      ]⟩,
    ⟨[771, 77501], [771, 77501], .contexts []⟩,
    ⟨[77503, 13], [77503, 13], .contexts []⟩,
    ⟨[773], [770], .source 451⟩,
    ⟨[773], [773], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 058. -/
def y322TCContextRaw058 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[773], [770], .contexts [
        ⟨3710, false, false, [], []⟩
      ]⟩,
    ⟨[770], [770], .contexts []⟩,
    ⟨[773], [770], .contexts [
        ⟨3711, false, false, [], []⟩,
        ⟨3712, false, false, [], []⟩,
        ⟨3713, false, false, [], []⟩,
        ⟨3713, false, false, [], []⟩
      ]⟩,
    ⟨[773, 77503], [773, 77503], .contexts []⟩,
    ⟨[77503, 13], [773, 77503], .contexts [
        ⟨3709, false, false, [], []⟩,
        ⟨3709, false, false, [], []⟩,
        ⟨2993, true, false, [], [13]⟩,
        ⟨3708, true, false, [770], [9, 13]⟩,
        ⟨3708, true, false, [770], [9, 13]⟩,
        ⟨3707, true, false, [770], [9, 13]⟩,
        ⟨3704, true, false, [770], [9, 13]⟩,
        ⟨1650, false, false, [770, 77501], []⟩,
        ⟨77, false, false, [770, 77501], []⟩,
        ⟨2993, false, false, [770], []⟩,
        ⟨3207, false, false, [770], []⟩,
        ⟨2996, false, false, [770], []⟩,
        ⟨2996, false, false, [770], []⟩,
        ⟨3714, true, false, [], [77503]⟩,
        ⟨3715, false, false, [], []⟩,
        ⟨3715, false, false, [], []⟩
      ]⟩,
    ⟨[77505, 13], [77505, 13], .contexts []⟩,
    ⟨[771], [772], .contexts [
        ⟨3710, true, true, [], []⟩
      ]⟩,
    ⟨[772], [772], .contexts []⟩,
    ⟨[771], [772], .contexts [
        ⟨3718, false, false, [], []⟩,
        ⟨3719, false, false, [], []⟩,
        ⟨3719, false, false, [], []⟩
      ]⟩,
    ⟨[771, 77505], [771, 77505], .contexts []⟩,
    ⟨[77505, 13, 1], [771, 77507], .contexts [
        ⟨3717, false, false, [], [1]⟩,
        ⟨3717, false, false, [], [1]⟩,
        ⟨2995, true, false, [], [13, 1]⟩,
        ⟨3716, true, false, [772], [11, 13, 1]⟩,
        ⟨1624, false, false, [772, 77503], [1]⟩,
        ⟨91, false, false, [772, 77503], [1]⟩,
        ⟨2999, false, false, [772], [1]⟩,
        ⟨3720, true, false, [], [77505, 1]⟩,
        ⟨3721, false, false, [], [1]⟩,
        ⟨3721, false, false, [], [1]⟩,
        ⟨3002, false, false, [771], []⟩
      ]⟩,
    ⟨[77505, 1], [77507], .contexts [
        ⟨3002, false, false, [], []⟩
      ]⟩,
    ⟨[77507, 13], [77509], .contexts [
        ⟨3004, false, false, [], []⟩
      ]⟩,
    ⟨[13, 1, 13, 1], [0, 12], .contexts [
        ⟨386, false, false, [], [0, 12]⟩
      ]⟩,
    ⟨[77509, 1], [77509, 1], .contexts []⟩,
    ⟨[77509], [77509], .contexts []⟩,
    ⟨[77509, 1], [773, 77509], .contexts [
        ⟨3726, false, false, [], []⟩,
        ⟨3004, true, false, [], [1]⟩,
        ⟨3722, true, false, [770], [13, 1]⟩,
        ⟨3725, false, false, [770, 77505], []⟩,
        ⟨388, false, false, [770, 77505], []⟩,
        ⟨3723, false, false, [770], [13]⟩,
        ⟨3205, false, false, [770], [13]⟩,
        ⟨3005, false, false, [770], [13]⟩,
        ⟨3005, false, false, [770], [13]⟩,
        ⟨3724, false, false, [770], []⟩,
        ⟨3204, false, false, [770], []⟩,
        ⟨3008, false, false, [770], []⟩,
        ⟨3008, false, false, [770], []⟩,
        ⟨3727, false, false, [770], []⟩,
        ⟨3714, true, false, [], [77509]⟩
      ]⟩,
    ⟨[773, 77509], [773, 77509], .contexts []⟩,
    ⟨[773, 77513], [773, 77513], .contexts []⟩,
    ⟨[1, 15, 1, 15], [], .contexts [
        ⟨198, false, false, [], []⟩
      ]⟩,
    ⟨[77513, 15], [771, 77509], .contexts [
        ⟨3730, true, false, [772], [15]⟩,
        ⟨3010, true, false, [], [15]⟩,
        ⟨3007, true, false, [], [1, 15]⟩,
        ⟨3729, true, false, [772], [15, 1, 15]⟩,
        ⟨3729, true, false, [772], [15, 1, 15]⟩,
        ⟨3728, true, false, [772], [15, 1, 15]⟩,
        ⟨3726, true, false, [772], [15, 1, 15]⟩,
        ⟨3731, false, false, [772, 77509], []⟩,
        ⟨3727, false, false, [772], []⟩,
        ⟨3720, true, false, [], [77509]⟩
      ]⟩,
    ⟨[773], [773], .contexts []⟩,
    ⟨[773], [773], .contexts []⟩,
    ⟨[77615], [77613, 9], .source 38872⟩,
    ⟨[77613, 9], [77615], .contexts [
        ⟨3735, true, false, [], []⟩
      ]⟩,
    ⟨[77615], [77615], .contexts []⟩,
    ⟨[77615], [77615], .contexts []⟩,
    ⟨[77615], [77615], .contexts []⟩,
    ⟨[77617], [77615, 11], .source 38873⟩,
    ⟨[77615, 11], [77617], .contexts [
        ⟨3740, true, false, [], []⟩
      ]⟩,
    ⟨[77617, 11], [77615], .contexts [
        ⟨3741, true, false, [], [11]⟩,
        ⟨90, false, false, [77615], []⟩,
        ⟨3738, false, false, [], []⟩
      ]⟩,
    ⟨[77617], [77617], .contexts []⟩,
    ⟨[77617], [77617], .contexts []⟩,
    ⟨[77619], [77617, 1], .source 38874⟩,
    ⟨[77617, 1], [77619], .contexts [
        ⟨3745, true, false, [], []⟩
      ]⟩,
    ⟨[77619, 1], [77617], .contexts [
        ⟨3746, true, false, [], [1]⟩,
        ⟨18, false, false, [77617], []⟩,
        ⟨3744, false, false, [], []⟩
      ]⟩,
    ⟨[77621], [77619, 13], .source 38875⟩,
    ⟨[77619, 13], [77621], .contexts [
        ⟨3748, true, false, [], []⟩
      ]⟩,
    ⟨[77619], [77619], .contexts []⟩,
    ⟨[77623], [77621, 15], .source 38876⟩,
    ⟨[77621, 15], [77623], .contexts [
        ⟨3751, true, false, [], []⟩
      ]⟩,
    ⟨[77621], [77621], .contexts []⟩,
    ⟨[77625], [77623, 1], .source 38877⟩,
    ⟨[77623, 1], [77625], .contexts [
        ⟨3754, true, false, [], []⟩
      ]⟩,
    ⟨[77623], [77623], .contexts []⟩,
    ⟨[77625, 1], [77623], .contexts [
        ⟨3755, true, false, [], [1]⟩,
        ⟨18, false, false, [77623], []⟩,
        ⟨3756, false, false, [], []⟩
      ]⟩,
    ⟨[77627], [77625, 3], .source 38878⟩,
    ⟨[77625, 3], [77627], .contexts [
        ⟨3758, true, false, [], []⟩
      ]⟩,
    ⟨[77625], [77625], .contexts []⟩,
    ⟨[77629], [77627, 5], .source 38879⟩,
    ⟨[77627, 5], [77629], .contexts [
        ⟨3761, true, false, [], []⟩
      ]⟩,
    ⟨[77627], [77627], .contexts []⟩,
    ⟨[77629, 5], [77627], .contexts [
        ⟨3762, true, false, [], [5]⟩,
        ⟨49, false, false, [77627], []⟩,
        ⟨3763, false, false, [], []⟩
      ]⟩,
    ⟨[77631], [77629, 1], .source 38880⟩,
    ⟨[77629, 1], [77631], .contexts [
        ⟨3765, true, false, [], []⟩
      ]⟩,
    ⟨[77629], [77629], .contexts []⟩,
    ⟨[77631, 1], [77629], .contexts [
        ⟨3766, true, false, [], [1]⟩,
        ⟨18, false, false, [77629], []⟩,
        ⟨3767, false, false, [], []⟩
      ]⟩,
    ⟨[77633], [77631, 9], .source 38881⟩,
    ⟨[77631, 9], [77633], .contexts [
        ⟨3769, true, false, [], []⟩
      ]⟩,
    ⟨[77631], [77631], .contexts []⟩,
    ⟨[77633, 9], [77631], .contexts [
        ⟨3770, true, false, [], [9]⟩,
        ⟨76, false, false, [77631], []⟩,
        ⟨3771, false, false, [], []⟩
      ]⟩,
    ⟨[77635], [77633, 11], .source 38882⟩,
    ⟨[77633, 11], [77635], .contexts [
        ⟨3773, true, false, [], []⟩
      ]⟩,
    ⟨[77633], [77633], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 059. -/
def y322TCContextRaw059 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77637], [77635, 1], .source 38883⟩,
    ⟨[77635, 1], [77637], .contexts [
        ⟨3776, true, false, [], []⟩
      ]⟩,
    ⟨[77635], [77635], .contexts []⟩,
    ⟨[77639], [77637, 13], .source 38884⟩,
    ⟨[77637, 13], [77639], .contexts [
        ⟨3779, true, false, [], []⟩
      ]⟩,
    ⟨[77637], [77637], .contexts []⟩,
    ⟨[77641], [77639, 15], .source 38885⟩,
    ⟨[77639, 15], [77641], .contexts [
        ⟨3782, true, false, [], []⟩
      ]⟩,
    ⟨[77639], [77639], .contexts []⟩,
    ⟨[77643], [77641, 1], .source 38886⟩,
    ⟨[77641, 1], [77643], .contexts [
        ⟨3785, true, false, [], []⟩
      ]⟩,
    ⟨[77641], [77641], .contexts []⟩,
    ⟨[77645], [77643, 3], .source 38887⟩,
    ⟨[77643, 3], [77645], .contexts [
        ⟨3788, true, false, [], []⟩
      ]⟩,
    ⟨[77643], [77643], .contexts []⟩,
    ⟨[77647], [77645, 5], .source 38888⟩,
    ⟨[77645, 5], [77647], .contexts [
        ⟨3791, true, false, [], []⟩
      ]⟩,
    ⟨[77645], [77645], .contexts []⟩,
    ⟨[77649], [77647, 1], .source 38889⟩,
    ⟨[77647, 1], [77649], .contexts [
        ⟨3794, true, false, [], []⟩
      ]⟩,
    ⟨[77647], [77647], .contexts []⟩,
    ⟨[77651], [77649, 9], .source 38890⟩,
    ⟨[77649, 9], [77651], .contexts [
        ⟨3797, true, false, [], []⟩
      ]⟩,
    ⟨[77649], [77649], .contexts []⟩,
    ⟨[77653], [77651, 11], .source 38891⟩,
    ⟨[77651, 11], [77653], .contexts [
        ⟨3800, true, false, [], []⟩
      ]⟩,
    ⟨[77651], [77651], .contexts []⟩,
    ⟨[77653, 11], [77651], .contexts [
        ⟨3801, true, false, [], [11]⟩,
        ⟨90, false, false, [77651], []⟩,
        ⟨3802, false, false, [], []⟩
      ]⟩,
    ⟨[77655], [77653, 1], .source 38892⟩,
    ⟨[77653, 1], [77655], .contexts [
        ⟨3804, true, false, [], []⟩
      ]⟩,
    ⟨[77653], [77653], .contexts []⟩,
    ⟨[77657], [77655, 13], .source 38893⟩,
    ⟨[77655, 13], [77657], .contexts [
        ⟨3807, true, false, [], []⟩
      ]⟩,
    ⟨[77655], [77655], .contexts []⟩,
    ⟨[77659], [77657, 15], .source 38894⟩,
    ⟨[77657, 15], [77659], .contexts [
        ⟨3810, true, false, [], []⟩
      ]⟩,
    ⟨[77657], [77657], .contexts []⟩,
    ⟨[77661], [77659, 1], .source 38895⟩,
    ⟨[77659, 1], [77661], .contexts [
        ⟨3813, true, false, [], []⟩
      ]⟩,
    ⟨[77659], [77659], .contexts []⟩,
    ⟨[77663], [77661, 3], .source 38896⟩,
    ⟨[77661, 3], [77663], .contexts [
        ⟨3816, true, false, [], []⟩
      ]⟩,
    ⟨[77661], [77661], .contexts []⟩,
    ⟨[77665], [77663, 5], .source 38897⟩,
    ⟨[77663], [77663], .contexts []⟩,
    ⟨[77665, 5], [77663], .contexts [
        ⟨3819, false, false, [], [5]⟩,
        ⟨49, false, false, [77663], []⟩,
        ⟨3820, false, false, [], []⟩
      ]⟩,
    ⟨[77667], [77665, 1], .source 38898⟩,
    ⟨[77665], [77665], .contexts []⟩,
    ⟨[77667, 1], [77665], .contexts [
        ⟨3822, false, false, [], [1]⟩,
        ⟨18, false, false, [77665], []⟩,
        ⟨3823, false, false, [], []⟩
      ]⟩,
    ⟨[77669], [77667, 9], .source 38899⟩,
    ⟨[77667, 9], [77669], .contexts [
        ⟨3825, true, false, [], []⟩
      ]⟩,
    ⟨[77667], [77667], .contexts []⟩,
    ⟨[77669, 9], [77667], .contexts [
        ⟨3826, true, false, [], [9]⟩,
        ⟨76, false, false, [77667], []⟩,
        ⟨3827, false, false, [], []⟩
      ]⟩,
    ⟨[77671], [77669, 11], .source 38900⟩,
    ⟨[77669, 11], [77671], .contexts [
        ⟨3829, true, false, [], []⟩
      ]⟩,
    ⟨[77669], [77669], .contexts []⟩,
    ⟨[77671, 11], [77669], .contexts [
        ⟨3830, true, false, [], [11]⟩,
        ⟨90, false, false, [77669], []⟩,
        ⟨3831, false, false, [], []⟩
      ]⟩,
    ⟨[77673], [77671, 1], .source 38901⟩,
    ⟨[77671], [77671], .contexts []⟩,
    ⟨[77673, 1], [77671], .contexts [
        ⟨3833, false, false, [], [1]⟩,
        ⟨18, false, false, [77671], []⟩,
        ⟨3834, false, false, [], []⟩
      ]⟩,
    ⟨[77675], [77673, 13], .source 38902⟩,
    ⟨[77673], [77673], .contexts []⟩,
    ⟨[77675, 13], [77673], .contexts [
        ⟨3836, false, false, [], [13]⟩,
        ⟨98, false, false, [77673], []⟩,
        ⟨3837, false, false, [], []⟩
      ]⟩,
    ⟨[77677], [77675, 15], .source 38903⟩]

/-- Exact literal claimed equations and contextual derivations, block 060. -/
def y322TCContextRaw060 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77675], [77675], .contexts []⟩,
    ⟨[77677, 15], [77675], .contexts [
        ⟨3839, false, false, [], [15]⟩,
        ⟨3, false, false, [77675], []⟩,
        ⟨3840, false, false, [], []⟩
      ]⟩,
    ⟨[77679], [77677, 1], .source 38904⟩,
    ⟨[77677, 1], [77679], .contexts [
        ⟨3842, true, false, [], []⟩
      ]⟩,
    ⟨[77677], [77677], .contexts []⟩,
    ⟨[77679, 1], [77677], .contexts [
        ⟨3843, true, false, [], [1]⟩,
        ⟨18, false, false, [77677], []⟩,
        ⟨3844, false, false, [], []⟩
      ]⟩,
    ⟨[77681], [77679, 3], .source 38905⟩,
    ⟨[77679], [77679], .contexts []⟩,
    ⟨[77681, 3], [77679], .contexts [
        ⟨3846, false, false, [], [3]⟩,
        ⟨35, false, false, [77679], []⟩,
        ⟨3847, false, false, [], []⟩
      ]⟩,
    ⟨[77683], [77681, 5], .source 38906⟩,
    ⟨[77681, 5], [77683], .contexts [
        ⟨3849, true, false, [], []⟩
      ]⟩,
    ⟨[77681], [77681], .contexts []⟩,
    ⟨[77683, 5], [77681], .contexts [
        ⟨3850, true, false, [], [5]⟩,
        ⟨49, false, false, [77681], []⟩,
        ⟨3851, false, false, [], []⟩
      ]⟩,
    ⟨[77685], [77683, 1], .source 38907⟩,
    ⟨[77683, 1], [77685], .contexts [
        ⟨3853, true, false, [], []⟩
      ]⟩,
    ⟨[77683], [77683], .contexts []⟩,
    ⟨[77685, 1], [77683], .contexts [
        ⟨3854, true, false, [], [1]⟩,
        ⟨18, false, false, [77683], []⟩,
        ⟨3855, false, false, [], []⟩
      ]⟩,
    ⟨[77687], [77685, 9], .source 38908⟩,
    ⟨[77685], [77685], .contexts []⟩,
    ⟨[77687, 9], [77685], .contexts [
        ⟨3857, false, false, [], [9]⟩,
        ⟨76, false, false, [77685], []⟩,
        ⟨3858, false, false, [], []⟩
      ]⟩,
    ⟨[77689], [77687, 11], .source 38909⟩,
    ⟨[77687], [77687], .contexts []⟩,
    ⟨[77689, 11], [77687], .contexts [
        ⟨3860, false, false, [], [11]⟩,
        ⟨90, false, false, [77687], []⟩,
        ⟨3861, false, false, [], []⟩
      ]⟩,
    ⟨[77691], [77689, 1], .source 38910⟩,
    ⟨[77689], [77689], .contexts []⟩,
    ⟨[77691, 1], [77689], .contexts [
        ⟨3863, false, false, [], [1]⟩,
        ⟨18, false, false, [77689], []⟩,
        ⟨3864, false, false, [], []⟩
      ]⟩,
    ⟨[77693], [77691, 13], .source 38911⟩,
    ⟨[77691], [77691], .contexts []⟩,
    ⟨[77693, 13], [77691], .contexts [
        ⟨3866, false, false, [], [13]⟩,
        ⟨98, false, false, [77691], []⟩,
        ⟨3867, false, false, [], []⟩
      ]⟩,
    ⟨[77695], [77693, 15], .source 38912⟩,
    ⟨[77693, 15], [77695], .contexts [
        ⟨3869, true, false, [], []⟩
      ]⟩,
    ⟨[77693], [77693], .contexts []⟩,
    ⟨[77695, 15], [77693], .contexts [
        ⟨3870, true, false, [], [15]⟩,
        ⟨3, false, false, [77693], []⟩,
        ⟨3871, false, false, [], []⟩
      ]⟩,
    ⟨[77697], [77695, 1], .source 38913⟩,
    ⟨[77695], [77695], .contexts []⟩,
    ⟨[77697, 1], [77695], .contexts [
        ⟨3873, false, false, [], [1]⟩,
        ⟨18, false, false, [77695], []⟩,
        ⟨3874, false, false, [], []⟩
      ]⟩,
    ⟨[77699], [77697, 3], .source 38914⟩,
    ⟨[77697], [77697], .contexts []⟩,
    ⟨[77699, 3], [77697], .contexts [
        ⟨3876, false, false, [], [3]⟩,
        ⟨35, false, false, [77697], []⟩,
        ⟨3877, false, false, [], []⟩
      ]⟩,
    ⟨[77701], [77699, 5], .source 38915⟩,
    ⟨[77699, 5], [77701], .contexts [
        ⟨3879, true, false, [], []⟩
      ]⟩,
    ⟨[77699], [77699], .contexts []⟩,
    ⟨[77701, 5], [77699], .contexts [
        ⟨3880, true, false, [], [5]⟩,
        ⟨49, false, false, [77699], []⟩,
        ⟨3881, false, false, [], []⟩
      ]⟩,
    ⟨[77703], [77701, 1], .source 38916⟩,
    ⟨[77701], [77701], .contexts []⟩,
    ⟨[77703, 1], [77701], .contexts [
        ⟨3883, false, false, [], [1]⟩,
        ⟨18, false, false, [77701], []⟩,
        ⟨3884, false, false, [], []⟩
      ]⟩,
    ⟨[77705], [77703, 9], .source 38917⟩,
    ⟨[77703, 9], [77705], .contexts [
        ⟨3886, true, false, [], []⟩
      ]⟩,
    ⟨[77703], [77703], .contexts []⟩,
    ⟨[77705, 9], [77703], .contexts [
        ⟨3887, true, false, [], [9]⟩,
        ⟨76, false, false, [77703], []⟩,
        ⟨3888, false, false, [], []⟩
      ]⟩,
    ⟨[77707], [77705, 11], .source 38918⟩,
    ⟨[77705], [77705], .contexts []⟩,
    ⟨[77707, 11], [77705], .contexts [
        ⟨3890, false, false, [], [11]⟩,
        ⟨90, false, false, [77705], []⟩,
        ⟨3891, false, false, [], []⟩
      ]⟩,
    ⟨[77709], [77707, 1], .source 38919⟩,
    ⟨[77707, 1], [77709], .contexts [
        ⟨3893, true, false, [], []⟩
      ]⟩,
    ⟨[77707], [77707], .contexts []⟩,
    ⟨[77709, 1], [77707], .contexts [
        ⟨3894, true, false, [], [1]⟩,
        ⟨18, false, false, [77707], []⟩,
        ⟨3895, false, false, [], []⟩
      ]⟩,
    ⟨[77711], [77709, 13], .source 38920⟩,
    ⟨[77709, 13], [77711], .contexts [
        ⟨3897, true, false, [], []⟩
      ]⟩,
    ⟨[77709], [77709], .contexts []⟩,
    ⟨[77711, 13], [77709], .contexts [
        ⟨3898, true, false, [], [13]⟩,
        ⟨98, false, false, [77709], []⟩,
        ⟨3899, false, false, [], []⟩
      ]⟩,
    ⟨[77711], [77711], .contexts []⟩,
    ⟨[77709, 1], [77707], .contexts [
        ⟨3896, false, false, [], []⟩,
        ⟨3895, false, false, [], []⟩,
        ⟨3895, false, false, [], []⟩
      ]⟩,
    ⟨[77707, 11], [77705], .contexts [
        ⟨3892, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 061. -/
def y322TCContextRaw061 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77705], [77705], .contexts []⟩,
    ⟨[77705, 9], [77703], .contexts [
        ⟨3889, false, false, [], []⟩
      ]⟩,
    ⟨[77703], [77703], .contexts []⟩,
    ⟨[77703, 1], [77701], .contexts [
        ⟨3885, false, false, [], []⟩
      ]⟩,
    ⟨[77701], [77701], .contexts []⟩,
    ⟨[77701, 5], [77699], .contexts [
        ⟨3882, false, false, [], []⟩
      ]⟩,
    ⟨[77699], [77699], .contexts []⟩,
    ⟨[77699, 3], [77697], .contexts [
        ⟨3878, false, false, [], []⟩
      ]⟩,
    ⟨[77697], [77697], .contexts []⟩,
    ⟨[77709, 1, 11, 9, 1, 5, 3], [77697], .contexts [
        ⟨3902, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨3903, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3904, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3891, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3891, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3905, false, false, [], [1, 5, 3]⟩,
        ⟨3906, false, false, [], [1, 5, 3]⟩,
        ⟨3888, false, false, [], [1, 5, 3]⟩,
        ⟨3888, false, false, [], [1, 5, 3]⟩,
        ⟨3907, false, false, [], [5, 3]⟩,
        ⟨3908, false, false, [], [5, 3]⟩,
        ⟨3884, false, false, [], [5, 3]⟩,
        ⟨3884, false, false, [], [5, 3]⟩,
        ⟨3909, false, false, [], [3]⟩,
        ⟨3910, false, false, [], [3]⟩,
        ⟨3881, false, false, [], [3]⟩,
        ⟨3881, false, false, [], [3]⟩,
        ⟨3911, false, false, [], []⟩,
        ⟨3912, false, false, [], []⟩,
        ⟨3877, false, false, [], []⟩,
        ⟨3877, false, false, [], []⟩
      ]⟩,
    ⟨[77697, 1], [77695], .contexts [
        ⟨3875, false, false, [], []⟩
      ]⟩,
    ⟨[77695], [77695], .contexts []⟩,
    ⟨[77693, 13], [77691], .contexts [
        ⟨3868, false, false, [], []⟩
      ]⟩,
    ⟨[77691], [77691], .contexts []⟩,
    ⟨[77691, 1], [77689], .contexts [
        ⟨3865, false, false, [], []⟩
      ]⟩,
    ⟨[77689], [77689], .contexts []⟩,
    ⟨[77689, 11], [77687], .contexts [
        ⟨3862, false, false, [], []⟩
      ]⟩,
    ⟨[77687], [77687], .contexts []⟩,
    ⟨[77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [77687], .contexts [
        ⟨3913, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨3914, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3915, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3874, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3874, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3872, false, false, [], [13, 1, 11]⟩,
        ⟨3871, false, false, [], [13, 1, 11]⟩,
        ⟨3871, false, false, [], [13, 1, 11]⟩,
        ⟨3916, false, false, [], [1, 11]⟩,
        ⟨3917, false, false, [], [1, 11]⟩,
        ⟨3867, false, false, [], [1, 11]⟩,
        ⟨3867, false, false, [], [1, 11]⟩,
        ⟨3918, false, false, [], [11]⟩,
        ⟨3919, false, false, [], [11]⟩,
        ⟨3864, false, false, [], [11]⟩,
        ⟨3864, false, false, [], [11]⟩,
        ⟨3920, false, false, [], []⟩,
        ⟨3921, false, false, [], []⟩,
        ⟨3861, false, false, [], []⟩,
        ⟨3861, false, false, [], []⟩
      ]⟩,
    ⟨[77687, 9], [77685], .contexts [
        ⟨3859, false, false, [], []⟩
      ]⟩,
    ⟨[77685], [77685], .contexts []⟩,
    ⟨[77683, 5], [77681], .contexts [
        ⟨3852, false, false, [], []⟩
      ]⟩,
    ⟨[77681], [77681], .contexts []⟩,
    ⟨[77681, 3], [77679], .contexts [
        ⟨3848, false, false, [], []⟩
      ]⟩,
    ⟨[77679], [77679], .contexts []⟩,
    ⟨[77679, 1], [77677], .contexts [
        ⟨3845, false, false, [], []⟩
      ]⟩,
    ⟨[77677], [77677], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [77677], .contexts [
        ⟨3922, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨3923, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3924, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3858, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3858, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3856, false, false, [], [5, 3, 1]⟩,
        ⟨3855, false, false, [], [5, 3, 1]⟩,
        ⟨3855, false, false, [], [5, 3, 1]⟩,
        ⟨3925, false, false, [], [3, 1]⟩,
        ⟨3926, false, false, [], [3, 1]⟩,
        ⟨3851, false, false, [], [3, 1]⟩,
        ⟨3851, false, false, [], [3, 1]⟩,
        ⟨3927, false, false, [], [1]⟩,
        ⟨3928, false, false, [], [1]⟩,
        ⟨3847, false, false, [], [1]⟩,
        ⟨3847, false, false, [], [1]⟩,
        ⟨3929, false, false, [], []⟩,
        ⟨3930, false, false, [], []⟩,
        ⟨3844, false, false, [], []⟩,
        ⟨3844, false, false, [], []⟩
      ]⟩,
    ⟨[77677, 15], [77675], .contexts [
        ⟨3841, false, false, [], []⟩
      ]⟩,
    ⟨[77675], [77675], .contexts []⟩,
    ⟨[77675, 13], [77673], .contexts [
        ⟨3838, false, false, [], []⟩
      ]⟩,
    ⟨[77673], [77673], .contexts []⟩,
    ⟨[77673, 1], [77671], .contexts [
        ⟨3835, false, false, [], []⟩
      ]⟩,
    ⟨[77671], [77671], .contexts []⟩,
    ⟨[77671, 11], [77669], .contexts [
        ⟨3832, false, false, [], []⟩
      ]⟩,
    ⟨[77669], [77669], .contexts []⟩,
    ⟨[77669, 9], [77667], .contexts [
        ⟨3828, false, false, [], []⟩
      ]⟩,
    ⟨[77667], [77667], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [77667], .contexts [
        ⟨3931, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨3932, false, false, [], [13, 1, 11, 9]⟩,
        ⟨3933, false, false, [], [13, 1, 11, 9]⟩,
        ⟨3840, false, false, [], [13, 1, 11, 9]⟩,
        ⟨3840, false, false, [], [13, 1, 11, 9]⟩,
        ⟨3934, false, false, [], [1, 11, 9]⟩,
        ⟨3935, false, false, [], [1, 11, 9]⟩,
        ⟨3837, false, false, [], [1, 11, 9]⟩,
        ⟨3837, false, false, [], [1, 11, 9]⟩,
        ⟨3936, false, false, [], [11, 9]⟩,
        ⟨3937, false, false, [], [11, 9]⟩,
        ⟨3834, false, false, [], [11, 9]⟩,
        ⟨3834, false, false, [], [11, 9]⟩,
        ⟨3938, false, false, [], [9]⟩,
        ⟨3939, false, false, [], [9]⟩,
        ⟨3831, false, false, [], [9]⟩,
        ⟨3831, false, false, [], [9]⟩,
        ⟨3940, false, false, [], []⟩,
        ⟨3941, false, false, [], []⟩,
        ⟨3827, false, false, [], []⟩,
        ⟨3827, false, false, [], []⟩
      ]⟩,
    ⟨[77663], [77663], .contexts []⟩,
    ⟨[77661], [77661], .contexts []⟩,
    ⟨[77659], [77659], .contexts []⟩,
    ⟨[77657], [77657], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [77657], .contexts [
        ⟨3942, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨3824, false, false, [], [5, 3, 1, 15]⟩,
        ⟨3823, false, false, [], [5, 3, 1, 15]⟩,
        ⟨3823, false, false, [], [5, 3, 1, 15]⟩,
        ⟨3821, false, false, [], [3, 1, 15]⟩,
        ⟨3943, false, false, [], [3, 1, 15]⟩,
        ⟨3820, false, false, [], [3, 1, 15]⟩,
        ⟨3820, false, false, [], [3, 1, 15]⟩,
        ⟨3817, true, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [77661], [1, 15]⟩,
        ⟨3818, false, false, [], [1, 15]⟩,
        ⟨3944, false, false, [], [1, 15]⟩,
        ⟨3818, false, false, [], [1, 15]⟩,
        ⟨3818, false, false, [], [1, 15]⟩,
        ⟨3814, true, false, [], [1, 15]⟩,
        ⟨18, false, false, [77659], [15]⟩,
        ⟨3815, false, false, [], [15]⟩,
        ⟨3945, false, false, [], [15]⟩,
        ⟨3815, false, false, [], [15]⟩,
        ⟨3815, false, false, [], [15]⟩,
        ⟨3811, true, false, [], [15]⟩,
        ⟨3, false, false, [77657], []⟩,
        ⟨3812, false, false, [], []⟩,
        ⟨3946, false, false, [], []⟩,
        ⟨3812, false, false, [], []⟩,
        ⟨3812, false, false, [], []⟩
      ]⟩,
    ⟨[77653], [77653], .contexts []⟩,
    ⟨[77651], [77651], .contexts []⟩,
    ⟨[77649], [77649], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [77649], .contexts [
        ⟨3947, false, false, [], [13, 1, 11, 9]⟩,
        ⟨3808, true, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [77655], [1, 11, 9]⟩,
        ⟨3809, false, false, [], [1, 11, 9]⟩,
        ⟨3809, false, false, [], [1, 11, 9]⟩,
        ⟨3809, false, false, [], [1, 11, 9]⟩,
        ⟨3805, true, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [77653], [11, 9]⟩,
        ⟨3806, false, false, [], [11, 9]⟩,
        ⟨3948, false, false, [], [11, 9]⟩,
        ⟨3806, false, false, [], [11, 9]⟩,
        ⟨3806, false, false, [], [11, 9]⟩,
        ⟨3803, false, false, [], [9]⟩,
        ⟨3949, false, false, [], [9]⟩,
        ⟨3802, false, false, [], [9]⟩,
        ⟨3802, false, false, [], [9]⟩,
        ⟨3798, true, false, [], [9]⟩,
        ⟨76, false, false, [77649], []⟩,
        ⟨3799, false, false, [], []⟩,
        ⟨3950, false, false, [], []⟩,
        ⟨3799, false, false, [], []⟩,
        ⟨3799, false, false, [], []⟩
      ]⟩,
    ⟨[77647], [77647], .contexts []⟩,
    ⟨[77645], [77645], .contexts []⟩,
    ⟨[77641], [77641], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [77641], .contexts [
        ⟨3951, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3795, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [77647], [5, 3, 1]⟩,
        ⟨3796, false, false, [], [5, 3, 1]⟩,
        ⟨3952, false, false, [], [5, 3, 1]⟩,
        ⟨3796, false, false, [], [5, 3, 1]⟩,
        ⟨3796, false, false, [], [5, 3, 1]⟩,
        ⟨3792, true, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [77645], [3, 1]⟩,
        ⟨3793, false, false, [], [3, 1]⟩,
        ⟨3953, false, false, [], [3, 1]⟩,
        ⟨3793, false, false, [], [3, 1]⟩,
        ⟨3793, false, false, [], [3, 1]⟩,
        ⟨3789, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [77643], [1]⟩,
        ⟨3790, false, false, [], [1]⟩,
        ⟨3790, false, false, [], [1]⟩,
        ⟨3790, false, false, [], [1]⟩,
        ⟨3786, true, false, [], [1]⟩,
        ⟨18, false, false, [77641], []⟩,
        ⟨3787, false, false, [], []⟩,
        ⟨3954, false, false, [], []⟩,
        ⟨3787, false, false, [], []⟩,
        ⟨3787, false, false, [], []⟩
      ]⟩,
    ⟨[77639], [77639], .contexts []⟩,
    ⟨[77637], [77637], .contexts []⟩,
    ⟨[77635], [77635], .contexts []⟩,
    ⟨[77633], [77633], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11
    ], [77633], .contexts [
        ⟨3955, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3783, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77639], [13, 1, 11]⟩,
        ⟨3784, false, false, [], [13, 1, 11]⟩,
        ⟨3956, false, false, [], [13, 1, 11]⟩,
        ⟨3784, false, false, [], [13, 1, 11]⟩,
        ⟨3784, false, false, [], [13, 1, 11]⟩,
        ⟨3780, true, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [77637], [1, 11]⟩,
        ⟨3781, false, false, [], [1, 11]⟩,
        ⟨3957, false, false, [], [1, 11]⟩,
        ⟨3781, false, false, [], [1, 11]⟩,
        ⟨3781, false, false, [], [1, 11]⟩,
        ⟨3777, true, false, [], [1, 11]⟩,
        ⟨18, false, false, [77635], [11]⟩,
        ⟨3778, false, false, [], [11]⟩,
        ⟨3958, false, false, [], [11]⟩,
        ⟨3778, false, false, [], [11]⟩,
        ⟨3778, false, false, [], [11]⟩,
        ⟨3774, true, false, [], [11]⟩,
        ⟨90, false, false, [77633], []⟩,
        ⟨3775, false, false, [], []⟩,
        ⟨3959, false, false, [], []⟩,
        ⟨3775, false, false, [], []⟩,
        ⟨3775, false, false, [], []⟩
      ]⟩,
    ⟨[77631], [77631], .contexts []⟩,
    ⟨[77629, 5], [77627], .contexts [
        ⟨3764, false, false, [], []⟩
      ]⟩,
    ⟨[77627], [77627], .contexts []⟩,
    ⟨[77627, 3], [77625], .contexts [
        ⟨3759, true, false, [], [3]⟩,
        ⟨35, false, false, [77625], []⟩,
        ⟨3760, false, false, [], []⟩
      ]⟩,
    ⟨[77625], [77625], .contexts []⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [77623], .contexts [
        ⟨3960, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨3772, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3961, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3771, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3771, false, false, [], [1, 5, 3, 1]⟩,
        ⟨3768, false, false, [], [5, 3, 1]⟩,
        ⟨3767, false, false, [], [5, 3, 1]⟩,
        ⟨3767, false, false, [], [5, 3, 1]⟩,
        ⟨3962, false, false, [], [3, 1]⟩,
        ⟨3963, false, false, [], [3, 1]⟩,
        ⟨3763, false, false, [], [3, 1]⟩,
        ⟨3763, false, false, [], [3, 1]⟩,
        ⟨3964, false, false, [], [1]⟩,
        ⟨3965, false, false, [], [1]⟩,
        ⟨3760, false, false, [], [1]⟩,
        ⟨3760, false, false, [], [1]⟩,
        ⟨3757, false, false, [], []⟩,
        ⟨3756, false, false, [], []⟩,
        ⟨3756, false, false, [], []⟩
      ]⟩,
    ⟨[77621], [77621], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 062. -/
def y322TCContextRaw062 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77621, 13], [77619], .contexts [
        ⟨3749, true, false, [], [13]⟩,
        ⟨98, false, false, [77619], []⟩,
        ⟨3750, false, false, [], []⟩
      ]⟩,
    ⟨[77619], [77619], .contexts []⟩,
    ⟨[77619, 1], [77617], .contexts [
        ⟨3747, false, false, [], []⟩
      ]⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [77615], .contexts [
        ⟨3966, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3752, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77621], [13, 1, 11]⟩,
        ⟨3753, false, false, [], [13, 1, 11]⟩,
        ⟨3967, false, false, [], [13, 1, 11]⟩,
        ⟨3753, false, false, [], [13, 1, 11]⟩,
        ⟨3753, false, false, [], [13, 1, 11]⟩,
        ⟨3968, false, false, [], [1, 11]⟩,
        ⟨3969, false, false, [], [1, 11]⟩,
        ⟨3750, false, false, [], [1, 11]⟩,
        ⟨3750, false, false, [], [1, 11]⟩,
        ⟨3970, false, false, [], [11]⟩,
        ⟨3743, false, false, [], [11]⟩,
        ⟨3744, false, false, [], [11]⟩,
        ⟨3744, false, false, [], [11]⟩,
        ⟨3742, false, false, [], []⟩,
        ⟨3737, false, false, [], []⟩,
        ⟨3738, false, false, [], []⟩,
        ⟨3738, false, false, [], []⟩
      ]⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [433, 77609], .contexts [
        ⟨3971, false, false, [], [9, 1, 5, 3]⟩,
        ⟨3736, true, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [77613], [1, 5, 3]⟩,
        ⟨3684, false, false, [], [1, 5, 3]⟩,
        ⟨3683, false, false, [], [1, 5, 3]⟩,
        ⟨3684, false, false, [], [1, 5, 3]⟩,
        ⟨3684, false, false, [], [1, 5, 3]⟩,
        ⟨3702, false, false, [], [5, 3]⟩,
        ⟨3686, false, false, [], [5, 3]⟩,
        ⟨3687, false, false, [], [5, 3]⟩,
        ⟨3687, false, false, [], [5, 3]⟩,
        ⟨3682, false, false, [433], [3]⟩,
        ⟨3664, false, false, [], [3]⟩,
        ⟨3665, false, false, [], [3]⟩,
        ⟨3666, false, false, [], [3]⟩,
        ⟨3658, false, false, [433], []⟩,
        ⟨3661, false, false, [], []⟩,
        ⟨3662, false, false, [], []⟩,
        ⟨3663, false, false, [], []⟩
      ]⟩,
    ⟨[775], [433, 451], .source 452⟩,
    ⟨[777], [775, 445], .source 453⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [777, 77471], .contexts [
        ⟨3972, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨3631, false, false, [433], [15, 13, 1, 11]⟩,
        ⟨3613, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3614, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3615, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3607, false, false, [433], [13, 1, 11]⟩,
        ⟨3611, false, false, [], [13, 1, 11]⟩,
        ⟨3612, false, false, [], [13, 1, 11]⟩,
        ⟨2277, false, false, [433], [1, 11]⟩,
        ⟨2485, false, false, [], [1, 11]⟩,
        ⟨2486, false, false, [], [1, 11]⟩,
        ⟨2487, false, false, [], [1, 11]⟩,
        ⟨2499, false, false, [433], [11]⟩,
        ⟨3973, true, false, [], [77471, 11]⟩,
        ⟨2475, false, false, [775], []⟩,
        ⟨3974, true, false, [], [77471]⟩
      ]⟩,
    ⟨[779], [777, 509], .source 454⟩,
    ⟨[781], [779, 257], .source 455⟩,
    ⟨[783], [781, 261], .source 456⟩,
    ⟨[785], [783, 503], .source 457⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [785, 77111], .contexts [
        ⟨3975, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨2710, false, false, [777], [1, 5, 3, 1]⟩,
        ⟨3976, true, false, [], [77485, 1, 5, 3, 1]⟩,
        ⟨2685, false, false, [779], [5, 3, 1]⟩,
        ⟨3977, true, false, [], [77485, 5, 3, 1]⟩,
        ⟨2697, false, false, [781], [3, 1]⟩,
        ⟨3978, true, false, [], [77485, 3, 1]⟩,
        ⟨2690, false, false, [783], [1]⟩,
        ⟨3979, true, false, [], [77113, 1]⟩,
        ⟨364, false, false, [785], []⟩
      ]⟩,
    ⟨[787], [785, 31], .source 458⟩,
    ⟨[789], [787, 19], .source 459⟩,
    ⟨[791], [789, 211], .source 460⟩,
    ⟨[793], [791, 217], .source 461⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [793, 77355], .contexts [
        ⟨3980, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨361, false, false, [785], [13, 1, 11, 9]⟩,
        ⟨740, true, false, [785], [77111, 13, 1, 11, 9]⟩,
        ⟨3981, true, false, [], [77111, 13, 1, 11, 9]⟩,
        ⟨354, false, false, [787], [1, 11, 9]⟩,
        ⟨735, true, false, [787], [77111, 1, 11, 9]⟩,
        ⟨3982, true, false, [], [77111, 1, 11, 9]⟩,
        ⟨363, false, false, [789], [11, 9]⟩,
        ⟨1526, false, false, [789], [9]⟩,
        ⟨3983, true, false, [], [77355, 9]⟩,
        ⟨1501, false, false, [791], []⟩,
        ⟨3984, true, false, [], [77355]⟩
      ]⟩,
    ⟨[795], [793, 209], .source 462⟩,
    ⟨[797], [795, 93], .source 463⟩,
    ⟨[799], [797, 87], .source 464⟩,
    ⟨[801], [799, 109], .source 465⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [801, 77227], .contexts [
        ⟨3985, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨1493, false, false, [793], [5, 3, 1, 15]⟩,
        ⟨3986, true, false, [], [77109, 5, 3, 1, 15]⟩,
        ⟨896, false, false, [795], [3, 1, 15]⟩,
        ⟨3987, true, false, [], [77225, 3, 1, 15]⟩,
        ⟨613, false, false, [797], [1, 15]⟩,
        ⟨809, false, false, [797], [15]⟩,
        ⟨3988, true, false, [], [77227, 15]⟩,
        ⟨840, false, false, [799], []⟩,
        ⟨3989, true, false, [], [77227]⟩
      ]⟩,
    ⟨[803], [801, 103], .source 466⟩,
    ⟨[805], [803, 87], .source 467⟩,
    ⟨[807], [805, 159], .source 468⟩,
    ⟨[809], [807, 87], .source 469⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [809, 77233], .contexts [
        ⟨3990, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨832, false, false, [801], [1, 11, 9, 1]⟩,
        ⟨3991, true, false, [], [77227, 1, 11, 9, 1]⟩,
        ⟨809, false, false, [803], [11, 9, 1]⟩,
        ⟨3992, true, false, [], [77227, 11, 9, 1]⟩,
        ⟨1073, false, false, [805], [9, 1]⟩,
        ⟨1097, false, false, [805], [1]⟩,
        ⟨3993, true, false, [], [77233, 1]⟩,
        ⟨1082, false, false, [807], []⟩,
        ⟨3994, true, false, [], [77233]⟩
      ]⟩,
    ⟨[811], [809, 81], .source 470⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3
    ], [811, 77235], .contexts [
        ⟨3995, false, false, [], [5, 3]⟩,
        ⟨1077, true, false, [809], [5, 3]⟩,
        ⟨1083, false, false, [809, 77227], [3]⟩,
        ⟨1084, false, false, [809, 77227], [3]⟩,
        ⟨617, false, false, [809], [11, 3]⟩,
        ⟨804, false, false, [809], [11, 3]⟩,
        ⟨800, false, false, [809], [11, 3]⟩,
        ⟨800, false, false, [809], [11, 3]⟩,
        ⟨800, false, false, [809], [11, 3]⟩,
        ⟨1073, false, false, [809, 81], [3]⟩,
        ⟨1080, false, false, [809, 81], [3]⟩,
        ⟨803, true, false, [809], [77233, 3]⟩,
        ⟨24, true, false, [809], [81, 77233, 3]⟩,
        ⟨3996, true, false, [], [77233, 3]⟩,
        ⟨1103, false, false, [811], []⟩
      ]⟩,
    ⟨[813], [811, 109], .source 471⟩,
    ⟨[815], [813, 285], .source 472⟩,
    ⟨[817], [815, 135], .source 473⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [817, 77215, 11], .contexts [
        ⟨3997, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨1820, false, false, [811], [15, 13, 1, 11]⟩,
        ⟨1834, false, false, [811], [13, 1, 11]⟩,
        ⟨3998, true, false, [], [77361, 13, 1, 11]⟩,
        ⟨1841, false, false, [813], [1, 11]⟩,
        ⟨3999, true, false, [], [77215, 1, 11]⟩,
        ⟨996, false, false, [815], [11]⟩,
        ⟨4000, true, false, [], [77215, 11]⟩
      ]⟩,
    ⟨[819], [817, 141], .source 474⟩,
    ⟨[821], [819, 135], .source 475⟩,
    ⟨[823], [821, 485], .source 476⟩,
    ⟨[825], [823, 253], .source 477⟩,
    ⟨[
      77709, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [825, 77347], .contexts [
        ⟨4001, false, false, [], [9, 1, 5, 3]⟩,
        ⟨595, false, false, [817], [9, 1, 5, 3]⟩,
        ⟨957, false, false, [817], [1, 5, 3]⟩,
        ⟨4002, true, false, [], [77217, 1, 5, 3]⟩,
        ⟨599, false, false, [819], [5, 3]⟩,
        ⟨954, false, false, [819], [5, 3]⟩,
        ⟨4003, true, false, [], [77217, 5, 3]⟩,
        ⟨2598, true, false, [821, 482], [5, 3]⟩,
        ⟨49, false, false, [821, 482, 77481], [3]⟩,
        ⟨2599, true, false, [821], [77481, 3]⟩,
        ⟨4004, true, false, [], [77481, 3]⟩,
        ⟨2593, false, false, [823], []⟩,
        ⟨4005, true, false, [], [77347]⟩
      ]⟩,
    ⟨[825, 77345], [825, 77345], .contexts []⟩,
    ⟨[825, 77345], [825, 77345], .contexts []⟩,
    ⟨[13, 15], [
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0
    ], .contexts [
        ⟨764, false, false, [0, 10, 8, 0, 4, 2, 0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0
        ]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨993, false, false, [], [
          8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
          2
        ]⟩,
        ⟨77, false, false, [1, 11], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [1, 11, 9], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [1, 11, 9, 1], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [1, 11, 9, 1, 5], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [1, 11, 9, 1, 5, 3], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [1, 11, 9, 1, 5, 3, 1], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [1, 11, 9, 1, 5, 3, 1, 15], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [1, 11, 9, 1, 5, 3, 1, 15, 13], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [0, 4, 2]⟩,
        ⟨19, false, false, [1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [4, 2]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨4010, false, false, [], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨4011, false, false, [], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨4012, false, false, [], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨4013, false, false, [], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨4014, false, false, [], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨4015, false, false, [], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2]⟩,
        ⟨50, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0
    ], [
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], .contexts [
        ⟨4016, false, false, [], [0]⟩,
        ⟨36, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0]⟩,
        ⟨19, false, false, [
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], []⟩
      ]⟩,
    ⟨[77711, 15], [77711, 15], .contexts []⟩,
    ⟨[77711, 15], [825, 77345], .contexts [
        ⟨4018, false, false, [], []⟩,
        ⟨3901, true, false, [], [15]⟩,
        ⟨3901, true, false, [], [15]⟩,
        ⟨3898, true, false, [], [15]⟩,
        ⟨4009, false, false, [77709], []⟩,
        ⟨4017, false, false, [77709], []⟩,
        ⟨4006, false, false, [], [1]⟩,
        ⟨1342, false, false, [825], []⟩,
        ⟨4007, false, false, [], []⟩,
        ⟨4008, false, false, [], []⟩,
        ⟨1589, false, false, [825], []⟩,
        ⟨24, true, false, [], [825, 77345]⟩
      ]⟩,
    ⟨[827], [824], .source 478⟩,
    ⟨[77345, 15], [827, 77711], .contexts [
        ⟨4019, true, false, [824], [15]⟩,
        ⟨3, false, false, [824, 77711], []⟩,
        ⟨4020, true, false, [], [77711]⟩
      ]⟩,
    ⟨[77711, 13], [77709], .contexts [
        ⟨3900, false, false, [], []⟩,
        ⟨3899, false, false, [], []⟩,
        ⟨3899, false, false, [], []⟩
      ]⟩,
    ⟨[77711, 15], [825, 77345], .contexts [
        ⟨4018, false, false, [], []⟩,
        ⟨4019, false, false, [], []⟩,
        ⟨4007, false, false, [], []⟩,
        ⟨4008, false, false, [], []⟩,
        ⟨4008, false, false, [], []⟩
      ]⟩,
    ⟨[829], [825, 269], .source 479⟩,
    ⟨[831], [829, 827], .source 480⟩,
    ⟨[831, 77709], [831, 77709], .contexts []⟩,
    ⟨[831, 77709], [831, 77709], .contexts []⟩,
    ⟨[77709, 15], [77709, 15], .contexts []⟩,
    ⟨[77709], [77709], .contexts []⟩,
    ⟨[831], [831], .contexts []⟩,
    ⟨[831], [831], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 063. -/
def y322TCContextRaw063 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[831], [831], .contexts [
        ⟨24, false, false, [], [831]⟩,
        ⟨4030, false, false, [], []⟩,
        ⟨4031, false, false, [], []⟩
      ]⟩,
    ⟨[833], [825, 491], .source 481⟩,
    ⟨[835], [833, 827], .source 482⟩,
    ⟨[77711], [77711], .contexts []⟩,
    ⟨[77711, 3], [77711, 3], .contexts []⟩,
    ⟨[77711], [77711], .contexts []⟩,
    ⟨[837], [834], .source 483⟩,
    ⟨[834], [834], .contexts []⟩,
    ⟨[77711, 3], [837, 77711], .contexts [
        ⟨4036, false, false, [], []⟩,
        ⟨4034, false, false, [834], [77711, 3]⟩,
        ⟨4021, true, false, [834, 833], [3]⟩,
        ⟨4033, false, false, [834], [77345, 15, 3]⟩,
        ⟨2614, true, false, [834, 825], [15, 3]⟩,
        ⟨4023, true, false, [834], [3, 15, 3]⟩,
        ⟨1555, false, false, [834, 77711], []⟩,
        ⟨4035, false, false, [834], []⟩,
        ⟨4037, false, false, [834], []⟩,
        ⟨4039, true, false, [], [77711]⟩,
        ⟨4039, true, false, [], [77711]⟩,
        ⟨4038, true, false, [], [77711]⟩
      ]⟩,
    ⟨[839], [825, 261], .source 484⟩,
    ⟨[841], [839, 827], .source 485⟩,
    ⟨[15, 5, 15, 5], [], .contexts [
        ⟨47, false, false, [], []⟩
      ]⟩,
    ⟨[77711, 5], [77711, 5], .contexts []⟩,
    ⟨[843], [840], .source 486⟩,
    ⟨[843], [843], .contexts []⟩,
    ⟨[840], [840], .contexts []⟩,
    ⟨[843], [840], .contexts [
        ⟨4046, false, false, [], []⟩,
        ⟨4045, false, false, [], []⟩,
        ⟨4047, false, false, [], []⟩,
        ⟨4047, false, false, [], []⟩
      ]⟩,
    ⟨[77711, 5], [843, 77711], .contexts [
        ⟨4044, false, false, [], []⟩,
        ⟨4042, false, false, [840], [77711, 5]⟩,
        ⟨4021, true, false, [840, 839], [5]⟩,
        ⟨4041, false, false, [840], [77345, 15, 5]⟩,
        ⟨1621, true, false, [840, 825], [15, 5]⟩,
        ⟨4023, true, false, [840], [5, 15, 5]⟩,
        ⟨4043, false, false, [840, 77711], []⟩,
        ⟨4035, false, false, [840], []⟩,
        ⟨4037, false, false, [840], []⟩,
        ⟨4048, true, false, [], [77711]⟩
      ]⟩,
    ⟨[845], [825, 537], .source 487⟩,
    ⟨[15, 11, 15, 11], [], .contexts [
        ⟨88, false, false, [], []⟩
      ]⟩,
    ⟨[847], [844], .source 488⟩,
    ⟨[844], [844], .contexts []⟩,
    ⟨[77123, 11], [847, 77711], .contexts [
        ⟨4050, false, false, [844], [77123, 11]⟩,
        ⟨2781, true, false, [844, 825], [11]⟩,
        ⟨1338, true, false, [844, 825], [15, 11]⟩,
        ⟨4023, true, false, [844], [11, 15, 11]⟩,
        ⟨4051, false, false, [844, 77711], []⟩,
        ⟨4035, false, false, [844], []⟩,
        ⟨4037, false, false, [844], []⟩,
        ⟨4053, true, false, [], [77711]⟩,
        ⟨4053, true, false, [], [77711]⟩,
        ⟨4052, true, false, [], [77711]⟩
      ]⟩,
    ⟨[77711, 11], [845, 77123], .contexts [
        ⟨4054, true, false, [846], [11]⟩,
        ⟨90, false, false, [846, 77123], []⟩,
        ⟨4052, false, true, [], [77123]⟩
      ]⟩,
    ⟨[77709, 15], [831, 77709], .contexts [
        ⟨4028, false, false, [], []⟩,
        ⟨4028, false, false, [], []⟩,
        ⟨4022, true, false, [], [15]⟩,
        ⟨148, false, false, [77711], []⟩,
        ⟨150, false, false, [77711], []⟩,
        ⟨4023, false, false, [], [13, 15, 13]⟩,
        ⟨1593, false, false, [825], [15, 13]⟩,
        ⟨4024, true, false, [], [77345, 15, 13]⟩,
        ⟨4021, false, false, [829], [13]⟩,
        ⟨4025, true, false, [], [77711, 13]⟩,
        ⟨3900, false, false, [831], []⟩,
        ⟨4026, false, false, [], []⟩,
        ⟨4027, false, false, [], []⟩,
        ⟨4029, false, false, [831], []⟩,
        ⟨4032, true, false, [], [77709]⟩,
        ⟨4026, false, false, [], []⟩,
        ⟨4027, false, false, [], []⟩
      ]⟩,
    ⟨[77709, 0], [77709, 1], .contexts [
        ⟨19, false, false, [77709], []⟩
      ]⟩,
    ⟨[77707, 15], [77707, 15], .contexts []⟩,
    ⟨[77707], [77707], .contexts []⟩,
    ⟨[849], [830], .source 489⟩,
    ⟨[830], [830], .contexts []⟩,
    ⟨[849], [830], .contexts [
        ⟨4060, false, false, [], []⟩,
        ⟨4061, false, false, [], []⟩,
        ⟨4061, false, false, [], []⟩
      ]⟩,
    ⟨[77707, 15], [849, 77707], .contexts [
        ⟨4058, false, false, [], []⟩,
        ⟨3896, true, false, [], [15]⟩,
        ⟨4027, true, false, [830], [1, 15]⟩,
        ⟨4056, true, false, [830], [1, 15]⟩,
        ⟨2778, false, false, [830, 77709], []⟩,
        ⟨4057, false, false, [830], []⟩,
        ⟨3902, false, false, [830], []⟩,
        ⟨4059, false, false, [830], []⟩,
        ⟨4062, true, false, [], [77707]⟩
      ]⟩,
    ⟨[837, 77711], [837, 77711], .contexts []⟩,
    ⟨[77711, 12], [77711, 13], .contexts [
        ⟨108, false, false, [77711], []⟩
      ]⟩,
    ⟨[836], [836], .contexts []⟩,
    ⟨[843, 77711], [843, 77711], .contexts []⟩,
    ⟨[77709, 5], [77709, 5], .contexts []⟩,
    ⟨[842], [842], .contexts []⟩,
    ⟨[841], [842], .contexts [
        ⟨4045, true, true, [], []⟩,
        ⟨4069, false, false, [], []⟩,
        ⟨4069, false, false, [], []⟩
      ]⟩,
    ⟨[849, 77707], [849, 77707], .contexts []⟩,
    ⟨[77707, 11], [77705], .contexts [
        ⟨3903, false, false, [], []⟩,
        ⟨3904, false, false, [], []⟩,
        ⟨3891, false, false, [], []⟩,
        ⟨3891, false, false, [], []⟩
      ]⟩,
    ⟨[77707, 10], [77707, 11], .contexts [
        ⟨91, false, false, [77707], []⟩
      ]⟩,
    ⟨[77705, 15], [77705, 15], .contexts []⟩,
    ⟨[77705], [77705], .contexts []⟩,
    ⟨[831], [848], .contexts [
        ⟨4060, true, true, [], []⟩
      ]⟩,
    ⟨[831], [831], .contexts []⟩,
    ⟨[848], [848], .contexts []⟩,
    ⟨[831], [848], .contexts [
        ⟨4077, false, false, [], []⟩,
        ⟨4076, false, false, [], []⟩,
        ⟨4078, false, false, [], []⟩,
        ⟨4078, false, false, [], []⟩
      ]⟩,
    ⟨[77705, 15], [831, 77705], .contexts [
        ⟨4074, false, false, [], []⟩,
        ⟨3892, true, false, [], [15]⟩,
        ⟨4071, true, false, [848], [11, 15]⟩,
        ⟨4071, true, false, [848], [11, 15]⟩,
        ⟨4063, true, false, [848], [11, 15]⟩,
        ⟨4058, true, false, [848], [11, 15]⟩,
        ⟨3495, false, false, [848, 77707], []⟩,
        ⟨4073, false, false, [848], []⟩,
        ⟨4072, false, false, [848], []⟩,
        ⟨4075, false, false, [848], []⟩,
        ⟨4079, true, false, [], [77705]⟩
      ]⟩,
    ⟨[841, 77709], [841, 77709], .contexts []⟩,
    ⟨[77709, 5], [841, 77709], .contexts [
        ⟨4068, false, false, [], []⟩,
        ⟨4068, false, false, [], []⟩,
        ⟨3900, true, false, [], [5]⟩,
        ⟨4067, true, false, [842], [13, 5]⟩,
        ⟨4067, true, false, [842], [13, 5]⟩,
        ⟨4049, true, false, [842], [13, 5]⟩,
        ⟨4044, true, false, [842], [13, 5]⟩,
        ⟨1578, false, false, [842, 77711], []⟩,
        ⟨4065, false, false, [842], []⟩,
        ⟨4022, false, false, [842], []⟩,
        ⟨4029, false, false, [842], []⟩,
        ⟨4070, true, false, [], [77709]⟩,
        ⟨4081, false, false, [], []⟩,
        ⟨4081, false, false, [], []⟩
      ]⟩,
    ⟨[77707, 5], [77707, 5], .contexts []⟩,
    ⟨[77707, 5], [843, 77707], .contexts [
        ⟨4083, false, false, [], []⟩,
        ⟨3896, true, false, [], [5]⟩,
        ⟨4082, true, false, [840], [1, 5]⟩,
        ⟨1509, false, false, [840, 77709], []⟩,
        ⟨4057, false, false, [840], []⟩,
        ⟨3902, false, false, [840], []⟩,
        ⟨4059, false, false, [840], []⟩,
        ⟨4048, true, false, [], [77707]⟩
      ]⟩,
    ⟨[831, 77705], [831, 77705], .contexts []⟩,
    ⟨[77705, 9], [77703], .contexts [
        ⟨3905, false, false, [], []⟩,
        ⟨3906, false, false, [], []⟩,
        ⟨3888, false, false, [], []⟩,
        ⟨3888, false, false, [], []⟩
      ]⟩,
    ⟨[77705, 8], [77705, 9], .contexts [
        ⟨77, false, false, [77705], []⟩
      ]⟩,
    ⟨[77703, 15], [77703, 15], .contexts []⟩,
    ⟨[77703], [77703], .contexts []⟩,
    ⟨[77703, 15], [849, 77703], .contexts [
        ⟨4088, false, false, [], []⟩,
        ⟨3889, true, false, [], [15]⟩,
        ⟨4085, true, false, [830], [9, 15]⟩,
        ⟨4085, true, false, [830], [9, 15]⟩,
        ⟨4080, true, false, [830], [9, 15]⟩,
        ⟨4074, true, false, [830], [9, 15]⟩,
        ⟨2787, false, false, [830, 77705], []⟩,
        ⟨4087, false, false, [830], []⟩,
        ⟨4086, false, false, [830], []⟩,
        ⟨4089, false, false, [830], []⟩,
        ⟨4062, true, false, [], [77703]⟩
      ]⟩,
    ⟨[843, 77707], [843, 77707], .contexts []⟩,
    ⟨[77705, 5], [77705, 5], .contexts []⟩,
    ⟨[77705, 5], [841, 77705], .contexts [
        ⟨4092, false, false, [], []⟩,
        ⟨3892, true, false, [], [5]⟩,
        ⟨4091, true, false, [842], [11, 5]⟩,
        ⟨4091, true, false, [842], [11, 5]⟩,
        ⟨4084, true, false, [842], [11, 5]⟩,
        ⟨4083, true, false, [842], [11, 5]⟩,
        ⟨1645, false, false, [842, 77707], []⟩,
        ⟨4073, false, false, [842], []⟩,
        ⟨4072, false, false, [842], []⟩,
        ⟨4075, false, false, [842], []⟩,
        ⟨4070, true, false, [], [77705]⟩
      ]⟩,
    ⟨[849, 77703], [849, 77703], .contexts []⟩,
    ⟨[77703, 1], [77701], .contexts [
        ⟨3907, false, false, [], []⟩
      ]⟩]

/-- Literal contextual derivation data in chronological chunk 00. -/
def y322TCContextRawChunk00 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCContextRaw000 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw001 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCContextRaw002 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw003 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCContextRaw004 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw005 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCContextRaw006 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw007 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCContextRaw008 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw009 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCContextRaw010 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw011 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCContextRaw012 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw013 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCContextRaw014 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw015 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCContextRaw016 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw017 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCContextRaw018 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw019 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCContextRaw020 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw021 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCContextRaw022 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw023 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCContextRaw024 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw025 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCContextRaw026 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw027 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCContextRaw028 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw029 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCContextRaw030 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw031 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCContextRaw032 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw033 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCContextRaw034 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw035 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCContextRaw036 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw037 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCContextRaw038 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw039 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCContextRaw040 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw041 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCContextRaw042 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw043 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCContextRaw044 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw045 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCContextRaw046 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw047 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCContextRaw048 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw049 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCContextRaw050 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw051 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCContextRaw052 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw053 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCContextRaw054 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw055 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCContextRaw056 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw057 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCContextRaw058 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw059 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCContextRaw060 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw061 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCContextRaw062 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw063 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
