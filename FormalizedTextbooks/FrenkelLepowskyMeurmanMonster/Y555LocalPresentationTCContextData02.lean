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

/-- Exact literal claimed equations and contextual derivations, block 128. -/
def y322TCContextRaw128 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78515, 3], [78513], .contexts [
        ⟨7902, false, false, [], []⟩,
        ⟨7903, false, false, [], []⟩,
        ⟨7848, false, false, [], []⟩,
        ⟨7848, false, false, [], []⟩
      ]⟩,
    ⟨[77679, 9], [1901, 78513], .contexts [
        ⟨8191, true, false, [1898], [9]⟩,
        ⟨3848, true, false, [], [9]⟩,
        ⟨8190, true, false, [1898], [3, 9]⟩,
        ⟨8190, true, false, [1898], [3, 9]⟩,
        ⟨8189, true, false, [1898], [3, 9]⟩,
        ⟨8169, true, false, [1898], [3, 9]⟩,
        ⟨8165, true, false, [1898], [3, 9]⟩,
        ⟨841, false, false, [1898, 78515], []⟩,
        ⟨36, false, false, [1898, 78515], []⟩,
        ⟨8192, false, false, [1898], []⟩,
        ⟨8185, false, false, [1898], []⟩,
        ⟨8138, true, false, [], [78513]⟩
      ]⟩,
    ⟨[1911, 78515], [1911, 78515], .contexts []⟩,
    ⟨[1895, 77569], [1895, 77569], .contexts []⟩,
    ⟨[77569, 9, 3], [1895, 77567], .contexts [
        ⟨8177, false, false, [], [3]⟩,
        ⟨8177, false, false, [], [3]⟩,
        ⟨3096, true, false, [], [9, 3]⟩,
        ⟨8176, true, false, [1892], [5, 9, 3]⟩,
        ⟨1034, false, false, [1892, 77571], [3]⟩,
        ⟨3557, false, false, [1892], [3]⟩,
        ⟨3556, false, false, [1892], [3]⟩,
        ⟨3559, false, false, [1892], [3]⟩,
        ⟨8178, true, false, [], [77569, 3]⟩,
        ⟨8178, true, false, [], [77569, 3]⟩,
        ⟨8077, true, false, [], [77569, 3]⟩,
        ⟨8078, true, false, [], [77569, 3]⟩,
        ⟨8195, false, false, [], [3]⟩,
        ⟨8195, false, false, [], [3]⟩,
        ⟨3092, false, false, [1895], []⟩
      ]⟩,
    ⟨[1927, 78513], [1927, 78513], .contexts []⟩,
    ⟨[1926], [1926], .contexts []⟩,
    ⟨[78509], [78509], .contexts []⟩,
    ⟨[78539], [78257, 7], .source 39334⟩,
    ⟨[78257, 7], [78539], .contexts [
        ⟨8200, true, false, [], []⟩
      ]⟩,
    ⟨[78539], [78539], .contexts []⟩,
    ⟨[78539], [78539], .contexts []⟩,
    ⟨[1421, 78413], [1421, 78413], .contexts []⟩,
    ⟨[1421, 78413], [1421, 78413], .contexts []⟩,
    ⟨[78539, 1], [78539, 1], .contexts []⟩,
    ⟨[78541], [78257, 9], .source 39335⟩,
    ⟨[78257, 9], [78541], .contexts [
        ⟨8207, true, false, [], []⟩
      ]⟩,
    ⟨[78541], [78541], .contexts []⟩,
    ⟨[78257, 9], [78541], .contexts [
        ⟨8208, false, false, [], []⟩,
        ⟨8209, false, false, [], []⟩,
        ⟨8209, false, false, [], []⟩
      ]⟩,
    ⟨[1935], [1421, 1065], .source 1032⟩,
    ⟨[1937], [1935, 1423], .source 1033⟩,
    ⟨[78541], [78541], .contexts []⟩,
    ⟨[78541, 1], [1937, 78541], .contexts [
        ⟨8210, true, false, [], [1]⟩,
        ⟨1143, false, false, [78257], []⟩,
        ⟨1146, false, false, [78257], []⟩,
        ⟨6647, false, false, [], [9, 1, 9]⟩,
        ⟨4887, false, false, [1421], [1, 9]⟩,
        ⟨8211, true, false, [], [77131, 1, 9]⟩,
        ⟨6645, false, false, [1935], [9]⟩,
        ⟨8212, true, false, [], [78257, 9]⟩,
        ⟨8208, false, false, [1937], []⟩,
        ⟨8213, false, false, [1937], []⟩,
        ⟨24, true, false, [], [1937, 78541]⟩
      ]⟩,
    ⟨[1903, 78521], [1903, 78521], .contexts []⟩,
    ⟨[1903, 78519], [1903, 78519], .contexts []⟩,
    ⟨[1903, 78519], [1903, 78519], .contexts []⟩,
    ⟨[78541, 3], [78541, 3], .contexts []⟩,
    ⟨[1903], [1903], .contexts []⟩,
    ⟨[1903], [1903], .contexts []⟩,
    ⟨[78541, 3], [1903, 78519], .contexts [
        ⟨8218, false, false, [], []⟩,
        ⟨8210, true, false, [], [3]⟩,
        ⟨306, false, false, [78257], []⟩,
        ⟨307, false, false, [78257], []⟩,
        ⟨8097, false, false, [], [9]⟩,
        ⟨8100, false, false, [], [9]⟩,
        ⟨8215, false, false, [], [9]⟩,
        ⟨8215, false, false, [], [9]⟩,
        ⟨7859, false, false, [1903], []⟩,
        ⟨8216, false, false, [], []⟩,
        ⟨8217, false, false, [], []⟩,
        ⟨8107, false, false, [1903], []⟩,
        ⟨8220, true, false, [], [78519]⟩,
        ⟨8219, true, false, [], [78519]⟩,
        ⟨24, true, false, [], [1903, 78519]⟩
      ]⟩,
    ⟨[1485, 77959], [1485, 77959], .contexts []⟩,
    ⟨[1485, 77959], [1485, 77959], .contexts []⟩,
    ⟨[78541, 13], [78541, 13], .contexts []⟩,
    ⟨[78541, 13], [1485, 77959], .contexts [
        ⟨8224, false, false, [], []⟩,
        ⟨8210, true, false, [], [13]⟩,
        ⟨315, false, false, [78257], []⟩,
        ⟨316, false, false, [78257], []⟩,
        ⟨6787, false, false, [], [9]⟩,
        ⟨6836, false, false, [1480], []⟩,
        ⟨5403, false, false, [1480], [1]⟩,
        ⟨5178, false, false, [1480], []⟩,
        ⟨5567, false, false, [1480], []⟩,
        ⟨5420, false, false, [1480], []⟩,
        ⟨5420, false, false, [1480], []⟩,
        ⟨5569, false, false, [1480, 1191], []⟩,
        ⟨6837, true, false, [], [1191, 77959]⟩,
        ⟨6838, true, false, [], [77959]⟩,
        ⟨8222, false, false, [], []⟩,
        ⟨8223, false, false, [], []⟩,
        ⟨8223, false, false, [], []⟩,
        ⟨5569, false, false, [1485], []⟩,
        ⟨24, true, false, [], [1485, 77959]⟩
      ]⟩,
    ⟨[78519, 13], [78519, 13], .contexts []⟩,
    ⟨[1941], [1905, 1485], .source 1035⟩,
    ⟨[78519, 13], [1941, 77957], .contexts [
        ⟨8226, false, false, [], []⟩,
        ⟨8217, true, false, [1902], [13]⟩,
        ⟨8217, true, false, [1902], [13]⟩,
        ⟨8216, true, false, [1902], [13]⟩,
        ⟨8221, true, false, [1902], [13]⟩,
        ⟨8218, true, false, [1902], [13]⟩,
        ⟨238, false, false, [1902, 78541], []⟩,
        ⟨239, false, false, [1902, 78541], []⟩,
        ⟨8224, false, false, [1902], [3]⟩,
        ⟨8225, false, false, [1902], [3]⟩,
        ⟨8222, false, false, [1902], [3]⟩,
        ⟨8223, false, false, [1902], [3]⟩,
        ⟨8223, false, false, [1902], [3]⟩,
        ⟨5126, false, false, [1902, 1485], []⟩,
        ⟨5434, false, false, [1902, 1485], []⟩,
        ⟨8101, true, false, [], [1485, 77957]⟩,
        ⟨8227, true, false, [], [77957]⟩
      ]⟩,
    ⟨[1941, 77957], [1941, 77957], .contexts []⟩,
    ⟨[1941, 77957], [1941, 77957], .contexts []⟩,
    ⟨[1945], [1941, 1199], .source 1037⟩,
    ⟨[77949], [1273, 77947], .contexts [
        ⟨5110, true, false, [], []⟩,
        ⟨5110, true, false, [], []⟩,
        ⟨5189, true, false, [], []⟩,
        ⟨5619, true, false, [], []⟩,
        ⟨5618, true, false, [1270], [1]⟩,
        ⟨18, false, false, [1270, 77947], []⟩,
        ⟨5607, true, false, [], [77947]⟩,
        ⟨5613, false, false, [], []⟩,
        ⟨5608, true, false, [], [77947]⟩,
        ⟨5614, false, false, [], []⟩
      ]⟩,
    ⟨[1947], [1945, 1273], .source 1038⟩,
    ⟨[77947, 13], [1946, 78517], .contexts [
        ⟨8233, false, false, [1946], [77947, 13]⟩,
        ⟨8232, true, false, [1946, 1945], [13]⟩,
        ⟨5111, true, false, [1946, 1945], [13]⟩,
        ⟨5115, true, false, [1946, 1945], [1, 13]⟩,
        ⟨8231, false, false, [1946], [77953, 13, 1, 13]⟩,
        ⟨5592, true, false, [1946, 1941], [13, 1, 13]⟩,
        ⟨5122, true, false, [1946, 1941], [13, 1, 13]⟩,
        ⟨8230, true, false, [1946], [1, 13, 1, 13]⟩,
        ⟨8230, true, false, [1946], [1, 13, 1, 13]⟩,
        ⟨8229, true, false, [1946], [1, 13, 1, 13]⟩,
        ⟨8228, true, false, [1946], [1, 13, 1, 13]⟩,
        ⟨8226, true, false, [1946], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [1946, 78519], []⟩,
        ⟨8144, false, false, [1946], []⟩,
        ⟨8143, false, false, [1946], []⟩
      ]⟩,
    ⟨[77947, 13], [77947, 13], .contexts []⟩,
    ⟨[1949], [1946], .source 1039⟩,
    ⟨[1946], [1946], .contexts []⟩,
    ⟨[77947, 13], [1949, 78517], .contexts [
        ⟨8235, false, false, [], []⟩,
        ⟨8234, false, false, [], []⟩,
        ⟨8134, false, false, [1946], []⟩,
        ⟨8237, true, false, [], [78517]⟩,
        ⟨8237, true, false, [], [78517]⟩,
        ⟨8236, true, false, [], [78517]⟩
      ]⟩,
    ⟨[1949, 78517], [1949, 78517], .contexts []⟩,
    ⟨[77947, 13], [1949, 78517], .contexts [
        ⟨8235, false, false, [], []⟩,
        ⟨8238, false, false, [], []⟩,
        ⟨8239, false, false, [], []⟩,
        ⟨8239, false, false, [], []⟩
      ]⟩,
    ⟨[1951], [1949, 1925], .source 1040⟩,
    ⟨[1953], [1951, 1947], .source 1041⟩,
    ⟨[13, 3, 13, 3], [], .contexts [
        ⟨106, false, false, [], []⟩
      ]⟩,
    ⟨[77947], [77947], .contexts []⟩,
    ⟨[77947, 3], [77947, 3], .contexts []⟩,
    ⟨[77947], [77947], .contexts []⟩,
    ⟨[1955], [1952], .source 1042⟩,
    ⟨[1952], [1952], .contexts []⟩,
    ⟨[77947, 3], [1955, 77947], .contexts [
        ⟨8245, false, false, [], []⟩,
        ⟨8242, false, false, [1952], [77947, 3]⟩,
        ⟨8236, true, true, [1952, 1951], [77947, 3]⟩,
        ⟨98, true, false, [1952, 1951, 1948, 77947], [3]⟩,
        ⟨8238, false, false, [1952, 1951, 1948], [13, 3]⟩,
        ⟨8241, false, false, [1952], [78517, 13, 3]⟩,
        ⟨8163, true, false, [1952, 1949], [13, 3]⟩,
        ⟨8240, true, false, [1952], [3, 13, 3]⟩,
        ⟨8243, false, false, [1952, 77947], []⟩,
        ⟨8244, false, false, [1952], []⟩,
        ⟨8246, false, false, [1952], []⟩,
        ⟨8248, true, false, [], [77947]⟩,
        ⟨8248, true, false, [], [77947]⟩,
        ⟨8247, true, false, [], [77947]⟩
      ]⟩,
    ⟨[1957], [1949, 1899], .source 1043⟩,
    ⟨[77947, 9], [77945], .contexts [
        ⟨5192, false, false, [], []⟩,
        ⟨5193, false, false, [], []⟩,
        ⟨5104, false, false, [], []⟩,
        ⟨5104, false, false, [], []⟩
      ]⟩,
    ⟨[77947, 8], [77947, 9], .contexts [
        ⟨77, false, false, [77947], []⟩
      ]⟩,
    ⟨[77683, 13], [77683, 13], .contexts []⟩,
    ⟨[77945], [77945], .contexts []⟩,
    ⟨[1959], [1956], .source 1044⟩]

/-- Exact literal claimed equations and contextual derivations, block 129. -/
def y322TCContextRaw129 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1956], [1956], .contexts []⟩,
    ⟨[77683, 13], [1959, 77945], .contexts [
        ⟨8253, false, false, [], []⟩,
        ⟨8250, false, false, [1956], [77683, 13]⟩,
        ⟨8140, false, false, [1956, 1949], [77683, 13]⟩,
        ⟨76, true, false, [1956, 1949, 1900, 77683], [13]⟩,
        ⟨8139, false, false, [1956, 1949, 1900], [9, 13]⟩,
        ⟨8240, true, false, [1956], [9, 13]⟩,
        ⟨1650, false, false, [1956, 77947], []⟩,
        ⟨8252, false, false, [1956], []⟩,
        ⟨8251, false, false, [1956], []⟩,
        ⟨8254, false, false, [1956], []⟩,
        ⟨8256, true, false, [], [77945]⟩,
        ⟨8256, true, false, [], [77945]⟩,
        ⟨8255, true, false, [], [77945]⟩
      ]⟩,
    ⟨[1957], [1958], .contexts [
        ⟨8255, true, true, [], []⟩
      ]⟩,
    ⟨[1955, 77947], [1955, 77947], .contexts []⟩,
    ⟨[1954], [1954], .contexts []⟩,
    ⟨[77683, 13], [1959, 77945], .contexts [
        ⟨8253, false, false, [], []⟩,
        ⟨8257, false, false, [], []⟩
      ]⟩,
    ⟨[1959, 77945], [1959, 77945], .contexts []⟩,
    ⟨[77683, 13], [1959, 77945], .contexts [
        ⟨8261, false, false, [], []⟩,
        ⟨8262, false, false, [], []⟩,
        ⟨8262, false, false, [], []⟩
      ]⟩,
    ⟨[1261, 77685], [1261, 77685], .contexts []⟩,
    ⟨[77683, 1, 13], [1261, 77685], .contexts [
        ⟨3854, false, false, [], [13]⟩,
        ⟨3924, false, false, [], [13]⟩,
        ⟨3858, false, false, [], [13]⟩,
        ⟨3858, false, false, [], [13]⟩,
        ⟨3859, true, false, [], [13]⟩,
        ⟨5598, true, false, [1264], [9, 13]⟩,
        ⟨5598, true, false, [1264], [9, 13]⟩,
        ⟨5590, true, false, [1264], [9, 13]⟩,
        ⟨5586, true, false, [1264], [9, 13]⟩,
        ⟨1650, false, false, [1264, 77687], []⟩,
        ⟨77, false, false, [1264, 77687], []⟩,
        ⟨3923, false, false, [1264], []⟩,
        ⟨3924, false, false, [1264], []⟩,
        ⟨3858, false, false, [1264], []⟩,
        ⟨3858, false, false, [1264], []⟩,
        ⟨5599, false, false, [1264], []⟩,
        ⟨5600, true, false, [], [77685]⟩,
        ⟨5600, true, false, [], [77685]⟩,
        ⟨5588, false, true, [], [77685]⟩,
        ⟨8264, false, false, [], []⟩,
        ⟨8264, false, false, [], []⟩
      ]⟩,
    ⟨[1961], [1957, 1261], .source 1045⟩,
    ⟨[1963], [1960], .source 1046⟩,
    ⟨[1965], [1957, 1963], .source 1047⟩,
    ⟨[77945], [1965, 77943], .contexts [
        ⟨8263, true, false, [1958], []⟩,
        ⟨8266, false, false, [1958, 1960], [77683, 13]⟩,
        ⟨8258, false, false, [1958, 1960], [1261, 77683, 13]⟩,
        ⟨7593, true, false, [1958, 1960, 1958, 1261], [13]⟩,
        ⟨3856, true, false, [1958, 1960, 1958, 1261], [13]⟩,
        ⟨8265, true, false, [1958, 1960, 1958], [1, 13]⟩,
        ⟨389, true, false, [1958, 1960, 1958, 77683], [13]⟩,
        ⟨3338, true, false, [1958, 1960, 1958, 77683], [13]⟩,
        ⟨8263, false, false, [1958, 1960, 1958], [1, 13, 13]⟩,
        ⟨5101, false, false, [1958, 1960], [13, 13]⟩,
        ⟨98, false, false, [1958, 1960, 77943], []⟩,
        ⟨8267, true, false, [1958], [77943]⟩,
        ⟨8258, true, false, [], [1963, 77943]⟩,
        ⟨8268, true, false, [], [77943]⟩
      ]⟩,
    ⟨[1967], [1964], .source 1048⟩,
    ⟨[1964], [1964], .contexts []⟩,
    ⟨[77943, 9], [1967, 77947], .contexts [
        ⟨8269, true, false, [1964], [9]⟩,
        ⟨5103, false, false, [1964], []⟩,
        ⟨5191, false, false, [1964], []⟩,
        ⟨8271, true, false, [], [77947]⟩,
        ⟨8271, true, false, [], [77947]⟩,
        ⟨8270, true, false, [], [77947]⟩
      ]⟩,
    ⟨[1965, 77943], [1965, 77943], .contexts []⟩,
    ⟨[77945], [1965, 77943], .contexts [
        ⟨8269, false, false, [], []⟩,
        ⟨8273, false, false, [], []⟩
      ]⟩,
    ⟨[1969], [1967, 1953], .source 1049⟩,
    ⟨[1971], [1969, 1965], .source 1050⟩,
    ⟨[1973], [1959, 1965], .source 1051⟩,
    ⟨[1975], [1972], .source 1052⟩,
    ⟨[1972], [1972], .contexts []⟩,
    ⟨[77941, 13], [1975, 77681], .contexts [
        ⟨5097, true, false, [], [13]⟩,
        ⟨8277, false, false, [1972], [77943, 5, 13]⟩,
        ⟨8274, true, false, [1972, 1959], [5, 13]⟩,
        ⟨8261, true, false, [1972], [5, 13]⟩,
        ⟨1886, false, false, [1972, 77683], []⟩,
        ⟨8164, false, false, [1972], []⟩,
        ⟨7607, false, false, [1972], []⟩,
        ⟨8166, false, false, [1972], []⟩,
        ⟨8279, true, false, [], [77681]⟩,
        ⟨8279, true, false, [], [77681]⟩,
        ⟨8278, true, false, [], [77681]⟩
      ]⟩,
    ⟨[77943, 3], [1971, 77943], .contexts [
        ⟨8269, true, false, [1964], [3]⟩,
        ⟨5105, true, false, [1964], [3]⟩,
        ⟨8259, true, false, [1964, 1954], [9, 3]⟩,
        ⟨8259, true, false, [1964, 1954], [9, 3]⟩,
        ⟨8249, true, false, [1964, 1954], [9, 3]⟩,
        ⟨8245, true, false, [1964, 1954], [9, 3]⟩,
        ⟨1010, false, false, [1964, 1954, 77947], []⟩,
        ⟨8252, false, false, [1964, 1954], []⟩,
        ⟨8251, false, false, [1964, 1954], []⟩,
        ⟨8254, false, false, [1964, 1954], []⟩,
        ⟨8260, true, false, [1964], [77945]⟩,
        ⟨8260, true, false, [1964], [77945]⟩,
        ⟨8247, false, true, [1964], [77945]⟩,
        ⟨8274, false, false, [1964, 1953], []⟩,
        ⟨8270, true, false, [], [1953, 1965, 77943]⟩,
        ⟨8275, true, false, [], [1965, 77943]⟩,
        ⟨8276, true, false, [], [77943]⟩
      ]⟩,
    ⟨[1971, 77943], [1971, 77943], .contexts []⟩,
    ⟨[77939, 5], [77939, 5], .contexts []⟩,
    ⟨[1977], [1970], .source 1053⟩,
    ⟨[1970], [1970], .contexts []⟩,
    ⟨[1977], [1970], .contexts [
        ⟨8284, false, false, [], []⟩,
        ⟨8285, false, false, [], []⟩,
        ⟨8285, false, false, [], []⟩
      ]⟩,
    ⟨[77939, 5], [1977, 77939], .contexts [
        ⟨8283, false, false, [], []⟩,
        ⟨5093, true, false, [], [5]⟩,
        ⟨5097, true, false, [], [3, 5]⟩,
        ⟨8282, true, false, [1970], [5, 3, 5]⟩,
        ⟨8282, true, false, [1970], [5, 3, 5]⟩,
        ⟨8281, true, false, [1970], [5, 3, 5]⟩,
        ⟨4744, false, false, [1970, 77943], []⟩,
        ⟨766, false, false, [1970, 77943], []⟩,
        ⟨5194, false, false, [1970], [3]⟩,
        ⟨5195, false, false, [1970], [3]⟩,
        ⟨5096, false, false, [1970], [3]⟩,
        ⟨5096, false, false, [1970], [3]⟩,
        ⟨5196, false, false, [1970], []⟩,
        ⟨5197, false, false, [1970], []⟩,
        ⟨5092, false, false, [1970], []⟩,
        ⟨5092, false, false, [1970], []⟩,
        ⟨8286, true, false, [], [77939]⟩
      ]⟩,
    ⟨[77941], [77941], .contexts []⟩,
    ⟨[77947, 1], [1271, 77951], .contexts [
        ⟨5618, false, false, [], []⟩
      ]⟩,
    ⟨[1967, 77947], [1967, 77947], .contexts []⟩,
    ⟨[1979], [1967, 1271], .source 1054⟩,
    ⟨[77951, 9], [77951, 9], .contexts []⟩,
    ⟨[1981], [1273, 1979], .source 1055⟩,
    ⟨[77951, 9], [1981, 77951], .contexts [
        ⟨8292, false, false, [], []⟩,
        ⟨5603, true, false, [1270], [9]⟩,
        ⟨5603, true, false, [1270], [9]⟩,
        ⟨5602, true, false, [1270], [9]⟩,
        ⟨8289, true, false, [1270], [9]⟩,
        ⟨8270, true, false, [1270, 1965], [77947, 1, 9]⟩,
        ⟨8272, true, false, [1270, 1965], [1, 9]⟩,
        ⟨8273, true, false, [1270], [9, 1, 9]⟩,
        ⟨8273, true, false, [1270], [9, 1, 9]⟩,
        ⟨8274, true, false, [1270], [9, 1, 9]⟩,
        ⟨5099, true, false, [1270], [9, 1, 9]⟩,
        ⟨1022, false, false, [1270, 77943], []⟩,
        ⟨787, false, false, [1270, 77943], []⟩,
        ⟨8272, false, false, [1270], [1]⟩,
        ⟨8290, false, false, [1270], [1]⟩,
        ⟨8290, false, false, [1270], [1]⟩,
        ⟨5618, false, false, [1270, 1967], []⟩,
        ⟨8291, true, false, [1270], [77951]⟩,
        ⟨5606, false, false, [1270, 1979], []⟩,
        ⟨5609, true, false, [], [1979, 77951]⟩,
        ⟨8293, true, false, [], [77951]⟩
      ]⟩,
    ⟨[1977, 77939], [1977, 77939], .contexts []⟩,
    ⟨[77937, 5], [77937, 5], .contexts []⟩,
    ⟨[1976], [1976], .contexts []⟩,
    ⟨[1971], [1976], .contexts [
        ⟨8284, true, true, [], []⟩,
        ⟨8297, false, false, [], []⟩,
        ⟨8297, false, false, [], []⟩
      ]⟩,
    ⟨[1981, 77951], [1981, 77951], .contexts []⟩,
    ⟨[1971, 77937], [1971, 77937], .contexts []⟩,
    ⟨[77937, 5], [1971, 77937], .contexts [
        ⟨8296, false, false, [], []⟩,
        ⟨8296, false, false, [], []⟩,
        ⟨5090, true, false, [], [5]⟩,
        ⟨8295, true, false, [1976], [1, 5]⟩,
        ⟨8295, true, false, [1976], [1, 5]⟩,
        ⟨8287, true, false, [1976], [1, 5]⟩,
        ⟨8283, true, false, [1976], [1, 5]⟩,
        ⟨1509, false, false, [1976, 77939], []⟩,
        ⟨19, false, false, [1976, 77939], []⟩,
        ⟨5199, false, false, [1976], []⟩,
        ⟨5200, false, false, [1976], []⟩,
        ⟨5089, false, false, [1976], []⟩,
        ⟨5089, false, false, [1976], []⟩,
        ⟨8298, true, false, [], [77937]⟩,
        ⟨8300, false, false, [], []⟩,
        ⟨8300, false, false, [], []⟩
      ]⟩,
    ⟨[77935, 5], [77935, 5], .contexts []⟩,
    ⟨[1977, 77935], [1977, 77935], .contexts []⟩,
    ⟨[77935, 5, 13], [1977, 77933], .contexts [
        ⟨8302, false, false, [], [13]⟩,
        ⟨8302, false, false, [], [13]⟩,
        ⟨5086, true, false, [], [5, 13]⟩,
        ⟨8301, true, false, [1970], [15, 5, 13]⟩,
        ⟨2006, false, false, [1970, 77937], [13]⟩,
        ⟨20, false, false, [1970, 77937], [13]⟩,
        ⟨5201, false, false, [1970], [13]⟩,
        ⟨5202, false, false, [1970], [13]⟩,
        ⟨5085, false, false, [1970], [13]⟩,
        ⟨5085, false, false, [1970], [13]⟩,
        ⟨8286, true, false, [], [77935, 13]⟩,
        ⟨8303, false, false, [], [13]⟩,
        ⟨8303, false, false, [], [13]⟩,
        ⟨5082, false, false, [1977], []⟩
      ]⟩,
    ⟨[77933, 5], [77933, 5], .contexts []⟩,
    ⟨[1971, 77933], [1971, 77933], .contexts []⟩,
    ⟨[1971, 77931, 5], [77933, 1], .contexts [
        ⟨5078, true, false, [1971], [5]⟩,
        ⟨8306, true, false, [], [1, 5]⟩,
        ⟨8306, true, false, [], [1, 5]⟩,
        ⟨8298, false, false, [], [77933, 1, 5]⟩,
        ⟨5081, true, false, [1976], [1, 5]⟩,
        ⟨5081, true, false, [1976], [1, 5]⟩,
        ⟨5204, true, false, [1976], [1, 5]⟩,
        ⟨5203, true, false, [1976], [1, 5]⟩,
        ⟨108, true, false, [1976, 77935], [1, 5]⟩,
        ⟨1578, true, false, [1976, 77935], [1, 5]⟩,
        ⟨8304, false, false, [1976], [5, 1, 5]⟩,
        ⟨8305, true, false, [], [1, 5]⟩,
        ⟨8305, true, false, [], [1, 5]⟩,
        ⟨1509, false, false, [77933], []⟩,
        ⟨19, false, false, [77933], []⟩
      ]⟩,
    ⟨[77931, 5], [77931, 5], .contexts []⟩,
    ⟨[1977, 77931], [1977, 77931], .contexts []⟩,
    ⟨[1977, 77929, 5], [77931, 11], .contexts [
        ⟨5074, true, false, [1977], [5]⟩,
        ⟨8309, true, false, [], [11, 5]⟩,
        ⟨8309, true, false, [], [11, 5]⟩,
        ⟨8286, false, false, [], [77931, 11, 5]⟩,
        ⟨5077, true, false, [1970], [11, 5]⟩,
        ⟨5077, true, false, [1970], [11, 5]⟩,
        ⟨5206, true, false, [1970], [11, 5]⟩,
        ⟨5205, true, false, [1970], [11, 5]⟩,
        ⟨8307, true, false, [1970], [11, 5]⟩,
        ⟨8308, true, false, [], [11, 5]⟩,
        ⟨8308, true, false, [], [11, 5]⟩,
        ⟨1645, false, false, [77931], []⟩,
        ⟨91, false, false, [77931], []⟩
      ]⟩,
    ⟨[77929, 5], [77929, 5], .contexts []⟩,
    ⟨[1971, 77929], [1971, 77929], .contexts []⟩,
    ⟨[1971, 77927], [1971, 77927], .contexts []⟩,
    ⟨[1971, 77927, 5], [77929, 9], .contexts [
        ⟨8313, true, false, [], [5]⟩,
        ⟨5070, true, false, [1971], [5]⟩,
        ⟨8312, true, false, [], [9, 5]⟩,
        ⟨8312, true, false, [], [9, 5]⟩,
        ⟨8298, false, false, [], [77929, 9, 5]⟩,
        ⟨5073, true, false, [1976], [9, 5]⟩,
        ⟨5073, true, false, [1976], [9, 5]⟩,
        ⟨5208, true, false, [1976], [9, 5]⟩,
        ⟨5207, true, false, [1976], [9, 5]⟩,
        ⟨8310, true, false, [1976], [9, 5]⟩,
        ⟨8311, true, false, [], [9, 5]⟩,
        ⟨8311, true, false, [], [9, 5]⟩,
        ⟨1672, false, false, [77929], []⟩,
        ⟨77, false, false, [77929], []⟩
      ]⟩,
    ⟨[77927, 5], [77927, 5], .contexts []⟩,
    ⟨[77927], [77927], .contexts []⟩,
    ⟨[1977, 77927], [1977, 77927], .contexts []⟩,
    ⟨[77927, 5, 1, 5], [1977, 77923], .contexts [
        ⟨8315, false, false, [], [1, 5]⟩,
        ⟨8315, false, false, [], [1, 5]⟩,
        ⟨8314, false, false, [1970], [1, 5]⟩,
        ⟨5210, false, false, [1970], [1, 5]⟩,
        ⟨5211, false, false, [1970], [1, 5]⟩,
        ⟨5069, false, false, [1970], [1, 5]⟩,
        ⟨5069, false, false, [1970], [1, 5]⟩,
        ⟨8316, false, false, [1970], [1, 5]⟩,
        ⟨8286, true, false, [], [77927, 1, 5]⟩,
        ⟨8317, false, false, [], [1, 5]⟩,
        ⟨8317, false, false, [], [1, 5]⟩,
        ⟨5066, false, false, [1977], [5]⟩,
        ⟨5063, false, false, [1977], []⟩
      ]⟩,
    ⟨[78543], [78407, 7], .source 39336⟩]

/-- Exact literal claimed equations and contextual derivations, block 130. -/
def y322TCContextRaw130 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78407, 7], [78543], .contexts [
        ⟨8319, true, false, [], []⟩
      ]⟩,
    ⟨[78407, 7], [78543], .contexts [
        ⟨8320, false, false, [], []⟩
      ]⟩,
    ⟨[78543], [78543], .contexts []⟩,
    ⟨[78543], [78543], .contexts []⟩,
    ⟨[78543], [78543], .contexts []⟩,
    ⟨[78405, 13], [78543], .contexts [
        ⟨1118, false, false, [], [78405, 13]⟩,
        ⟨7530, true, false, [], [13]⟩,
        ⟨7524, true, false, [], [13]⟩,
        ⟨7524, true, false, [], [13]⟩,
        ⟨7523, true, false, [], [13]⟩,
        ⟨7522, true, false, [], [13]⟩,
        ⟨6750, true, false, [], [7, 13]⟩,
        ⟨6750, true, false, [], [7, 13]⟩,
        ⟨6749, true, false, [], [7, 13]⟩,
        ⟨6750, true, false, [], [7, 13]⟩,
        ⟨98, true, false, [78259], [7, 13]⟩,
        ⟨7533, false, false, [], [13, 7, 13]⟩,
        ⟨1786, true, false, [78407], [13]⟩,
        ⟨1785, true, false, [78407], [13]⟩,
        ⟨8321, false, false, [], [13, 13]⟩,
        ⟨8322, false, false, [], [13, 13]⟩,
        ⟨8323, false, false, [], [13, 13]⟩,
        ⟨8323, false, false, [], [13, 13]⟩,
        ⟨98, false, false, [78543], []⟩,
        ⟨8323, false, false, [], []⟩
      ]⟩,
    ⟨[78545], [78407, 15], .source 39337⟩,
    ⟨[78407, 15], [78545], .contexts [
        ⟨8326, true, false, [], []⟩
      ]⟩,
    ⟨[78545], [78545], .contexts []⟩,
    ⟨[78545], [78545], .contexts []⟩,
    ⟨[78407, 15], [78545], .contexts [
        ⟨8327, false, false, [], []⟩,
        ⟨8328, false, false, [], []⟩,
        ⟨8329, false, false, [], []⟩,
        ⟨8329, false, false, [], []⟩
      ]⟩,
    ⟨[78545, 3], [78545, 3], .contexts []⟩,
    ⟨[77133], [77133], .contexts [
        ⟨2009, false, false, [], []⟩
      ]⟩,
    ⟨[77133], [77133], .contexts [
        ⟨1118, true, false, [], [77133]⟩
      ]⟩,
    ⟨[78545, 3], [77133], .contexts [
        ⟨8331, false, false, [], []⟩,
        ⟨8330, true, false, [], [3]⟩,
        ⟨34, false, false, [78407], []⟩,
        ⟨37, false, false, [78407], []⟩,
        ⟨7537, false, false, [], [15]⟩,
        ⟨7540, false, false, [], [15]⟩,
        ⟨720, false, false, [], [15]⟩,
        ⟨446, false, false, [], [15]⟩,
        ⟨446, false, false, [], [15]⟩,
        ⟨2004, false, false, [], []⟩,
        ⟨719, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨8332, false, false, [], []⟩,
        ⟨8333, false, false, [], []⟩
      ]⟩,
    ⟨[77133, 3], [78545], .contexts [
        ⟨8334, true, false, [], [3]⟩,
        ⟨35, false, false, [78545], []⟩,
        ⟨8329, false, false, [], []⟩
      ]⟩,
    ⟨[1753, 77259], [1753, 77259], .contexts []⟩,
    ⟨[1753, 77259], [1753, 77259], .contexts []⟩,
    ⟨[1753, 77261], [1753, 77261], .contexts []⟩,
    ⟨[1753, 77261], [1753, 77261], .contexts []⟩,
    ⟨[78545, 5], [78545, 5], .contexts []⟩,
    ⟨[78545, 5], [1753, 77261], .contexts [
        ⟨8340, false, false, [], []⟩,
        ⟨8330, true, false, [], [5]⟩,
        ⟨48, false, false, [78407], []⟩,
        ⟨51, false, false, [78407], []⟩,
        ⟨7542, false, false, [], [15]⟩,
        ⟨7544, false, false, [], [15]⟩,
        ⟨8336, false, false, [], [15]⟩,
        ⟨8337, false, false, [], [15]⟩,
        ⟨8337, false, false, [], [15]⟩,
        ⟨1207, false, false, [1753], []⟩,
        ⟨8338, false, false, [], []⟩,
        ⟨8339, false, false, [], []⟩,
        ⟨1755, false, false, [1753], []⟩,
        ⟨7543, true, false, [], [77261]⟩
      ]⟩,
    ⟨[77261, 5], [1755, 78545], .contexts [
        ⟨8341, true, false, [1752], [5]⟩,
        ⟨49, false, false, [1752, 78545], []⟩,
        ⟨7545, true, false, [], [78545]⟩
      ]⟩,
    ⟨[78545], [78545], .contexts []⟩,
    ⟨[78545, 3], [77133], .contexts [
        ⟨8331, false, false, [], []⟩,
        ⟨8334, false, false, [], []⟩,
        ⟨719, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩
      ]⟩,
    ⟨[77133, 13], [539, 77869], .contexts [
        ⟨4930, false, false, [], []⟩
      ]⟩,
    ⟨[539, 77869], [539, 77869], .contexts []⟩,
    ⟨[539, 77869], [539, 77869], .contexts []⟩,
    ⟨[539, 77871], [539, 77871], .contexts []⟩,
    ⟨[539, 77871], [539, 77871], .contexts []⟩,
    ⟨[538], [538], .contexts []⟩,
    ⟨[78545, 13], [539, 77871], .contexts [
        ⟨2792, false, false, [536], [78545, 13]⟩,
        ⟨8350, false, false, [536], [78545, 13]⟩,
        ⟨8350, false, false, [536], [78545, 13]⟩,
        ⟨8343, true, false, [536, 538], [13]⟩,
        ⟨3290, true, false, [536, 538, 78545], [13]⟩,
        ⟨8344, false, false, [536, 538], [13, 3, 13, 13]⟩,
        ⟨8345, false, false, [536, 538], [3, 13, 13]⟩,
        ⟨8346, false, false, [536, 538], [3, 13, 13]⟩,
        ⟨8347, false, false, [536, 538], [3, 13, 13]⟩,
        ⟨8347, false, false, [536, 538], [3, 13, 13]⟩,
        ⟨4949, false, false, [536], [13, 13]⟩,
        ⟨8348, false, false, [536, 538], [13, 13]⟩,
        ⟨8349, false, false, [536, 538], [13, 13]⟩,
        ⟨98, false, false, [536, 77871], []⟩,
        ⟨2782, true, false, [], [77871]⟩
      ]⟩,
    ⟨[78545, 5], [1753, 77261], .contexts [
        ⟨8341, false, false, [], []⟩
      ]⟩,
    ⟨[78545, 5], [1753, 77261], .contexts [
        ⟨8340, false, false, [], []⟩,
        ⟨8352, false, false, [], []⟩,
        ⟨8338, false, false, [], []⟩,
        ⟨8339, false, false, [], []⟩,
        ⟨8339, false, false, [], []⟩
      ]⟩,
    ⟨[1755], [1752], .contexts [
        ⟨7545, false, false, [], []⟩
      ]⟩,
    ⟨[1985], [1755, 539], .source 1057⟩,
    ⟨[77261, 13], [1985, 77873], .contexts [
        ⟨8353, true, false, [1752], [13]⟩,
        ⟨283, false, false, [1752, 78545], []⟩,
        ⟨284, false, false, [1752, 78545], []⟩,
        ⟨8351, false, false, [1752], [5]⟩,
        ⟨8348, false, false, [1752], [5]⟩,
        ⟨8349, false, false, [1752], [5]⟩,
        ⟨8349, false, false, [1752], [5]⟩,
        ⟨4962, false, false, [1752, 539], []⟩,
        ⟨4966, false, false, [1752, 539], []⟩,
        ⟨8354, true, false, [], [539, 77873]⟩,
        ⟨8355, true, false, [], [77873]⟩
      ]⟩,
    ⟨[1987], [1984], .source 1058⟩,
    ⟨[78547], [78413, 5], .source 39338⟩,
    ⟨[78413, 5], [78547], .contexts [
        ⟨8358, true, false, [], []⟩
      ]⟩,
    ⟨[78413, 5], [78547], .contexts [
        ⟨8359, false, false, [], []⟩
      ]⟩,
    ⟨[78547], [78547], .contexts []⟩,
    ⟨[78547], [78547], .contexts []⟩,
    ⟨[78547], [78547], .contexts []⟩,
    ⟨[78413, 13], [78261], .contexts [
        ⟨7672, true, false, [], [13]⟩,
        ⟨98, false, false, [78261], []⟩,
        ⟨6777, false, false, [], []⟩,
        ⟨6776, false, false, [], []⟩,
        ⟨6777, false, false, [], []⟩,
        ⟨6777, false, false, [], []⟩
      ]⟩,
    ⟨[78411], [78411], .contexts []⟩,
    ⟨[78411], [78411], .contexts [
        ⟨1118, true, false, [], [78411]⟩
      ]⟩,
    ⟨[78549], [78413, 11], .source 39339⟩,
    ⟨[78413, 11], [78549], .contexts [
        ⟨8367, true, false, [], []⟩
      ]⟩,
    ⟨[78549], [78549], .contexts []⟩,
    ⟨[78549], [78549], .contexts []⟩,
    ⟨[78551], [78413, 15], .source 39340⟩,
    ⟨[78413, 15], [78551], .contexts [
        ⟨8371, true, false, [], []⟩
      ]⟩,
    ⟨[78551], [78551], .contexts []⟩,
    ⟨[78551], [78551], .contexts []⟩,
    ⟨[78551, 7], [78551, 7], .contexts []⟩,
    ⟨[78551, 7], [77133], .contexts [
        ⟨8375, false, false, [], []⟩,
        ⟨8374, true, false, [], [7]⟩,
        ⟨8374, true, false, [], [7]⟩,
        ⟨8373, true, false, [], [7]⟩,
        ⟨8372, true, false, [], [7]⟩,
        ⟨61, false, false, [78413], []⟩,
        ⟨64, false, false, [78413], []⟩,
        ⟨7675, false, false, [], [15]⟩,
        ⟨7676, false, false, [], [15]⟩,
        ⟨720, false, false, [], [15]⟩,
        ⟨446, false, false, [], [15]⟩,
        ⟨446, false, false, [], [15]⟩,
        ⟨2004, false, false, [], []⟩,
        ⟨719, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨8332, false, false, [], []⟩,
        ⟨8333, false, false, [], []⟩
      ]⟩,
    ⟨[77133, 7], [78551], .contexts [
        ⟨8376, true, false, [], [7]⟩,
        ⟨62, false, false, [78551], []⟩,
        ⟨8374, false, false, [], []⟩
      ]⟩,
    ⟨[78553], [78521, 5], .source 39341⟩,
    ⟨[78521, 5], [78553], .contexts [
        ⟨8378, true, false, [], []⟩
      ]⟩,
    ⟨[78553, 5], [78521], .contexts [
        ⟨8379, true, false, [], [5]⟩,
        ⟨49, false, false, [78521], []⟩,
        ⟨7862, false, false, [], []⟩
      ]⟩,
    ⟨[78553], [78553], .contexts []⟩,
    ⟨[1905, 78257], [1905, 78257], .contexts []⟩,
    ⟨[1885, 77137], [1885, 77137], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 131. -/
def y322TCContextRaw131 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1885, 77139], [1885, 77139], .contexts []⟩,
    ⟨[1885, 77139], [1885, 77139], .contexts []⟩,
    ⟨[78553, 15], [78553, 15], .contexts []⟩,
    ⟨[1885], [1885], .contexts []⟩,
    ⟨[1885], [1885], .contexts []⟩,
    ⟨[1885], [1885], .contexts [
        ⟨24, false, false, [], [1885]⟩,
        ⟨8387, false, false, [], []⟩,
        ⟨8388, false, false, [], []⟩
      ]⟩,
    ⟨[78553, 15], [1885, 77139], .contexts [
        ⟨8386, false, false, [], []⟩,
        ⟨8381, true, false, [], [15]⟩,
        ⟨8381, true, false, [], [15]⟩,
        ⟨8379, true, false, [], [15]⟩,
        ⟨290, false, false, [78521], []⟩,
        ⟨291, false, false, [78521], []⟩,
        ⟨8063, false, false, [], [5]⟩,
        ⟨8066, false, false, [], [5]⟩,
        ⟨8383, false, false, [], [5]⟩,
        ⟨8383, false, false, [], [5]⟩,
        ⟨456, false, false, [1885], []⟩,
        ⟨8384, false, false, [], []⟩,
        ⟨8385, false, false, [], []⟩,
        ⟨2020, false, false, [1885], []⟩,
        ⟨8389, true, false, [], [77139]⟩
      ]⟩,
    ⟨[77139, 15], [1887, 78553], .contexts [
        ⟨8390, true, false, [1884], [15]⟩,
        ⟨3, false, false, [1884, 78553], []⟩,
        ⟨8067, true, false, [], [78553]⟩
      ]⟩,
    ⟨[78555], [78553, 1], .source 39342⟩,
    ⟨[78553, 1], [78555], .contexts [
        ⟨8392, true, false, [], []⟩
      ]⟩,
    ⟨[78555, 1], [78553], .contexts [
        ⟨8393, true, false, [], [1]⟩,
        ⟨18, false, false, [78553], []⟩,
        ⟨8381, false, false, [], []⟩
      ]⟩,
    ⟨[78555], [78555], .contexts []⟩,
    ⟨[78555], [78555], .contexts []⟩,
    ⟨[78553, 1], [78555], .contexts [
        ⟨8393, false, false, [], []⟩,
        ⟨8395, false, false, [], []⟩,
        ⟨8396, false, false, [], []⟩,
        ⟨8396, false, false, [], []⟩
      ]⟩,
    ⟨[78555, 5], [78555, 5], .contexts []⟩,
    ⟨[1899], [1899], .contexts []⟩,
    ⟨[1899], [1899], .contexts []⟩,
    ⟨[1899], [1899], .contexts [
        ⟨24, false, false, [], [1899]⟩,
        ⟨8399, false, false, [], []⟩,
        ⟨8400, false, false, [], []⟩
      ]⟩,
    ⟨[78555, 5], [1899, 77687], .contexts [
        ⟨8398, false, false, [], []⟩,
        ⟨8397, true, false, [], [5]⟩,
        ⟨165, false, false, [78553], []⟩,
        ⟨166, false, false, [78553], []⟩,
        ⟨8380, false, false, [], [1]⟩,
        ⟨7895, false, false, [], [1]⟩,
        ⟨7862, false, false, [], [1]⟩,
        ⟨7862, false, false, [], [1]⟩,
        ⟨8120, false, false, [], []⟩,
        ⟨8121, false, false, [], []⟩,
        ⟨8122, false, false, [], []⟩,
        ⟨8122, false, false, [], []⟩,
        ⟨5587, false, false, [1899], []⟩,
        ⟨8401, true, false, [], [77687]⟩
      ]⟩,
    ⟨[1885, 77141], [1885, 77141], .contexts []⟩,
    ⟨[1885, 77141], [1885, 77141], .contexts []⟩,
    ⟨[78555, 15], [78555, 15], .contexts []⟩,
    ⟨[77141], [77141], .contexts []⟩,
    ⟨[78555, 15], [1885, 77141], .contexts [
        ⟨8405, false, false, [], []⟩,
        ⟨8397, true, false, [], [15]⟩,
        ⟨199, false, false, [78553], []⟩,
        ⟨200, false, false, [78553], []⟩,
        ⟨8386, false, false, [], [1]⟩,
        ⟨8390, false, false, [], [1]⟩,
        ⟨8384, false, false, [], [1]⟩,
        ⟨8385, false, false, [], [1]⟩,
        ⟨8385, false, false, [], [1]⟩,
        ⟨459, false, false, [1885], []⟩,
        ⟨8403, false, false, [], []⟩,
        ⟨8404, false, false, [], []⟩,
        ⟨8406, false, false, [1885], []⟩,
        ⟨8389, true, false, [], [77141]⟩
      ]⟩,
    ⟨[77141, 15], [1887, 78555], .contexts [
        ⟨8407, true, false, [1884], [15]⟩,
        ⟨3, false, false, [1884, 78555], []⟩,
        ⟨8067, true, false, [], [78555]⟩
      ]⟩,
    ⟨[78555, 5], [1899, 77687], .contexts [
        ⟨8398, false, false, [], []⟩,
        ⟨8402, false, false, [], []⟩,
        ⟨8121, false, false, [], []⟩,
        ⟨8122, false, false, [], []⟩,
        ⟨8122, false, false, [], []⟩
      ]⟩,
    ⟨[1899, 77687, 13], [1899, 1265, 77687], .contexts [
        ⟨5590, false, false, [1899], []⟩
      ]⟩,
    ⟨[1899, 1265, 77687], [1899, 1265, 77687], .contexts []⟩,
    ⟨[1899, 1265, 77687], [1899, 1265, 77687], .contexts []⟩,
    ⟨[1993], [1899, 1265], .source 1061⟩,
    ⟨[1899, 1265, 77687], [1993, 77687], .contexts [
        ⟨8413, true, false, [], [77687]⟩
      ]⟩,
    ⟨[1995], [1993, 1901], .source 1062⟩,
    ⟨[5, 13, 5, 13], [], .contexts [
        ⟨282, false, false, [], []⟩
      ]⟩,
    ⟨[78555, 13], [78555, 13], .contexts []⟩,
    ⟨[78555], [78555], .contexts []⟩,
    ⟨[1997], [1994], .source 1063⟩,
    ⟨[1994], [1994], .contexts []⟩,
    ⟨[78555, 13], [1997, 78555], .contexts [
        ⟨8417, false, false, [], []⟩,
        ⟨8415, false, false, [1994], [78555, 13]⟩,
        ⟨8094, false, false, [1994, 1993], [78555, 13]⟩,
        ⟨49, true, false, [1994, 1993, 1898, 78555], [13]⟩,
        ⟨8402, false, false, [1994, 1993, 1898], [5, 13]⟩,
        ⟨8414, true, false, [1994], [5, 13]⟩,
        ⟨8412, true, false, [1994], [5, 13]⟩,
        ⟨8411, true, false, [1994], [5, 13]⟩,
        ⟨8410, true, false, [1994], [5, 13]⟩,
        ⟨8409, true, false, [1994], [13, 5, 13]⟩,
        ⟨8416, false, false, [1994, 78555], []⟩,
        ⟨8418, false, false, [1994], []⟩,
        ⟨8420, true, false, [], [78555]⟩,
        ⟨8420, true, false, [], [78555]⟩,
        ⟨8419, true, false, [], [78555]⟩
      ]⟩,
    ⟨[78557], [78555, 9], .source 39343⟩,
    ⟨[78555, 9], [78557], .contexts [
        ⟨8422, true, false, [], []⟩
      ]⟩,
    ⟨[78557, 9], [78555], .contexts [
        ⟨8423, true, false, [], [9]⟩,
        ⟨76, false, false, [78555], []⟩,
        ⟨8396, false, false, [], []⟩
      ]⟩,
    ⟨[78557], [78557], .contexts []⟩,
    ⟨[78557], [78557], .contexts []⟩,
    ⟨[78555, 9], [78557], .contexts [
        ⟨8423, false, false, [], []⟩,
        ⟨8425, false, false, [], []⟩,
        ⟨8426, false, false, [], []⟩,
        ⟨8426, false, false, [], []⟩
      ]⟩,
    ⟨[78557, 5], [78557, 5], .contexts []⟩,
    ⟨[78557, 5], [1899, 77685], .contexts [
        ⟨8428, false, false, [], []⟩,
        ⟨8427, true, false, [], [5]⟩,
        ⟨1805, false, false, [78555], []⟩,
        ⟨1806, false, false, [78555], []⟩,
        ⟨8409, false, false, [], [9]⟩,
        ⟨8124, false, false, [], []⟩,
        ⟨8125, false, false, [], []⟩,
        ⟨8126, false, false, [], []⟩,
        ⟨8127, false, false, [], []⟩,
        ⟨5599, false, false, [1899], []⟩,
        ⟨8401, true, false, [], [77685]⟩
      ]⟩,
    ⟨[1997, 78555], [1997, 78555], .contexts []⟩,
    ⟨[1997, 78557], [1997, 78557], .contexts []⟩,
    ⟨[1997, 78557], [1997, 78557], .contexts []⟩,
    ⟨[78557, 13], [78557, 13], .contexts []⟩,
    ⟨[78557], [78557], .contexts []⟩,
    ⟨[1997], [1997], .contexts [
        ⟨24, false, false, [], [1997]⟩
      ]⟩,
    ⟨[78557, 13], [1997, 78557], .contexts [
        ⟨8433, false, false, [], []⟩,
        ⟨8427, true, false, [], [13]⟩,
        ⟨315, false, false, [78555], []⟩,
        ⟨316, false, false, [78555], []⟩,
        ⟨8417, false, false, [], [9]⟩,
        ⟨8421, false, false, [], [9]⟩,
        ⟨8430, false, false, [], [9]⟩,
        ⟨8430, false, false, [], [9]⟩,
        ⟨8423, false, false, [1997], []⟩,
        ⟨8431, false, false, [], []⟩,
        ⟨8432, false, false, [], []⟩,
        ⟨8434, false, false, [1997], []⟩,
        ⟨8435, true, false, [], [78557]⟩
      ]⟩,
    ⟨[1885, 77143], [1885, 77143], .contexts []⟩,
    ⟨[1885, 77143], [1885, 77143], .contexts []⟩,
    ⟨[78557, 15], [78557, 15], .contexts []⟩,
    ⟨[77143], [77143], .contexts []⟩,
    ⟨[78557, 15], [1885, 77143], .contexts [
        ⟨8439, false, false, [], []⟩,
        ⟨8427, true, false, [], [15]⟩,
        ⟨323, false, false, [78555], []⟩,
        ⟨324, false, false, [78555], []⟩,
        ⟨8405, false, false, [], [9]⟩,
        ⟨8407, false, false, [], [9]⟩,
        ⟨8403, false, false, [], [9]⟩,
        ⟨8404, false, false, [], [9]⟩,
        ⟨8404, false, false, [], [9]⟩,
        ⟨462, false, false, [1885], []⟩,
        ⟨8437, false, false, [], []⟩,
        ⟨8438, false, false, [], []⟩,
        ⟨8440, false, false, [1885], []⟩,
        ⟨8389, true, false, [], [77143]⟩
      ]⟩,
    ⟨[77143, 15], [1887, 78557], .contexts [
        ⟨8441, true, false, [1884], [15]⟩,
        ⟨3, false, false, [1884, 78557], []⟩,
        ⟨8067, true, false, [], [78557]⟩
      ]⟩,
    ⟨[77681, 1], [1901, 78557], .contexts [
        ⟨8190, true, false, [1898], [1]⟩,
        ⟨8189, true, false, [1898], [1]⟩,
        ⟨3852, true, false, [], [1]⟩,
        ⟨8131, true, false, [1898], [5, 1]⟩,
        ⟨8130, true, false, [1898], [5, 1]⟩,
        ⟨8129, true, false, [1898], [5, 1]⟩,
        ⟨8128, true, false, [1898], [5, 1]⟩,
        ⟨8127, true, false, [1898], [1, 5, 1]⟩,
        ⟨8127, true, false, [1898], [1, 5, 1]⟩,
        ⟨8125, true, false, [1898], [1, 5, 1]⟩,
        ⟨8429, true, false, [1898], [1, 5, 1]⟩,
        ⟨8428, true, false, [1898], [1, 5, 1]⟩,
        ⟨1485, false, false, [1898, 78557], []⟩,
        ⟨8434, false, false, [1898], []⟩,
        ⟨8138, true, false, [], [78557]⟩
      ]⟩,
    ⟨[78557, 1], [1899, 77681], .contexts [
        ⟨8443, true, false, [1900], [1]⟩,
        ⟨18, false, false, [1900, 77681], []⟩,
        ⟨8140, true, false, [], [77681]⟩
      ]⟩,
    ⟨[78559], [78557, 11], .source 39344⟩,
    ⟨[78557, 11], [78559], .contexts [
        ⟨8445, true, false, [], []⟩
      ]⟩,
    ⟨[78559, 11], [78557], .contexts [
        ⟨8446, true, false, [], [11]⟩,
        ⟨90, false, false, [78557], []⟩,
        ⟨8426, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 132. -/
def y322TCContextRaw132 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78559], [78559], .contexts []⟩,
    ⟨[78559], [78559], .contexts []⟩,
    ⟨[78557, 11], [78559], .contexts [
        ⟨8446, false, false, [], []⟩,
        ⟨8448, false, false, [], []⟩,
        ⟨8449, false, false, [], []⟩,
        ⟨8449, false, false, [], []⟩
      ]⟩,
    ⟨[1997, 78559], [1997, 78559], .contexts []⟩,
    ⟨[1997, 78559], [1997, 78559], .contexts []⟩,
    ⟨[78559], [78559], .contexts []⟩,
    ⟨[78559, 13], [1997, 78559], .contexts [
        ⟨8450, true, false, [], [13]⟩,
        ⟨352, false, false, [78557], []⟩,
        ⟨353, false, false, [78557], []⟩,
        ⟨8433, false, false, [], [11]⟩,
        ⟨8436, false, false, [], [11]⟩,
        ⟨8431, false, false, [], [11]⟩,
        ⟨8432, false, false, [], [11]⟩,
        ⟨8432, false, false, [], [11]⟩,
        ⟨8446, false, false, [1997], []⟩,
        ⟨8451, false, false, [], []⟩,
        ⟨8452, false, false, [], []⟩,
        ⟨8453, false, false, [1997], []⟩,
        ⟨8435, true, false, [], [78559]⟩
      ]⟩,
    ⟨[1885, 77145], [1885, 77145], .contexts []⟩,
    ⟨[1885, 77145], [1885, 77145], .contexts []⟩,
    ⟨[78559, 15], [78559, 15], .contexts []⟩,
    ⟨[77145], [77145], .contexts []⟩,
    ⟨[78559, 15], [1885, 77145], .contexts [
        ⟨8457, false, false, [], []⟩,
        ⟨8450, true, false, [], [15]⟩,
        ⟨358, false, false, [78557], []⟩,
        ⟨359, false, false, [78557], []⟩,
        ⟨8439, false, false, [], [11]⟩,
        ⟨8441, false, false, [], [11]⟩,
        ⟨8437, false, false, [], [11]⟩,
        ⟨8438, false, false, [], [11]⟩,
        ⟨8438, false, false, [], [11]⟩,
        ⟨466, false, false, [1885], []⟩,
        ⟨8455, false, false, [], []⟩,
        ⟨8456, false, false, [], []⟩,
        ⟨8458, false, false, [1885], []⟩,
        ⟨8389, true, false, [], [77145]⟩
      ]⟩,
    ⟨[77145, 15], [1887, 78559], .contexts [
        ⟨8459, true, false, [1884], [15]⟩,
        ⟨3, false, false, [1884, 78559], []⟩,
        ⟨8067, true, false, [], [78559]⟩
      ]⟩,
    ⟨[78561], [78559, 1], .source 39345⟩,
    ⟨[78559, 1], [78561], .contexts [
        ⟨8461, true, false, [], []⟩
      ]⟩,
    ⟨[78561, 1], [78559], .contexts [
        ⟨8462, true, false, [], [1]⟩,
        ⟨18, false, false, [78559], []⟩,
        ⟨8449, false, false, [], []⟩
      ]⟩,
    ⟨[78561], [78561], .contexts []⟩,
    ⟨[78561], [78561], .contexts []⟩,
    ⟨[78559, 1], [78561], .contexts [
        ⟨8462, false, false, [], []⟩,
        ⟨8464, false, false, [], []⟩,
        ⟨8465, false, false, [], []⟩,
        ⟨8465, false, false, [], []⟩
      ]⟩,
    ⟨[78561, 11], [78561, 11], .contexts []⟩,
    ⟨[78561, 11], [1899, 77681], .contexts [
        ⟨8467, false, false, [], []⟩,
        ⟨8466, true, false, [], [11]⟩,
        ⟨181, false, false, [78559], []⟩,
        ⟨182, false, false, [78559], []⟩,
        ⟨8447, false, false, [], [1]⟩,
        ⟨8425, false, false, [], [1]⟩,
        ⟨8426, false, false, [], [1]⟩,
        ⟨8426, false, false, [], [1]⟩,
        ⟨8444, false, false, [], []⟩,
        ⟨8189, false, false, [], []⟩,
        ⟨8190, false, false, [], []⟩,
        ⟨8190, false, false, [], []⟩,
        ⟨8166, false, false, [1899], []⟩,
        ⟨8401, true, false, [], [77681]⟩
      ]⟩,
    ⟨[77681, 11], [1901, 78561], .contexts [
        ⟨8468, true, false, [1898], [11]⟩,
        ⟨90, false, false, [1898, 78561], []⟩,
        ⟨8094, true, false, [], [78561]⟩
      ]⟩,
    ⟨[1885, 77147], [1885, 77147], .contexts []⟩,
    ⟨[1885, 77147], [1885, 77147], .contexts []⟩,
    ⟨[78561, 15], [78561, 15], .contexts []⟩,
    ⟨[77147], [77147], .contexts []⟩,
    ⟨[78561, 15], [1885, 77147], .contexts [
        ⟨8472, false, false, [], []⟩,
        ⟨8466, true, false, [], [15]⟩,
        ⟨199, false, false, [78559], []⟩,
        ⟨200, false, false, [78559], []⟩,
        ⟨8457, false, false, [], [1]⟩,
        ⟨8459, false, false, [], [1]⟩,
        ⟨8455, false, false, [], [1]⟩,
        ⟨8456, false, false, [], [1]⟩,
        ⟨8456, false, false, [], [1]⟩,
        ⟨469, false, false, [1885], []⟩,
        ⟨8470, false, false, [], []⟩,
        ⟨8471, false, false, [], []⟩,
        ⟨8473, false, false, [1885], []⟩,
        ⟨8389, true, false, [], [77147]⟩
      ]⟩,
    ⟨[77147, 15], [1887, 78561], .contexts [
        ⟨8474, true, false, [1884], [15]⟩,
        ⟨3, false, false, [1884, 78561], []⟩,
        ⟨8067, true, false, [], [78561]⟩
      ]⟩,
    ⟨[78561, 11], [1899, 77681], .contexts [
        ⟨8467, false, false, [], []⟩,
        ⟨8468, false, false, [], []⟩,
        ⟨8189, false, false, [], []⟩,
        ⟨8190, false, false, [], []⟩,
        ⟨8190, false, false, [], []⟩
      ]⟩,
    ⟨[78561, 11, 9, 11], [1911, 78515], .contexts [
        ⟨8476, false, false, [], [9, 11]⟩,
        ⟨8170, false, false, [1899], [11]⟩,
        ⟨8094, false, false, [1899], [78515, 11]⟩,
        ⟨7852, true, false, [], [11]⟩,
        ⟨8171, true, false, [1918], [5, 11]⟩,
        ⟨8171, true, false, [1918], [5, 11]⟩,
        ⟨8148, true, false, [1918], [5, 11]⟩,
        ⟨8145, true, false, [1918], [5, 11]⟩,
        ⟨1028, false, false, [1918, 78517], []⟩,
        ⟨50, false, false, [1918, 78517], []⟩,
        ⟨8172, false, false, [1918], []⟩,
        ⟨8173, false, false, [1918], []⟩,
        ⟨8174, true, false, [], [78515]⟩,
        ⟨8174, true, false, [], [78515]⟩,
        ⟨8146, false, true, [], [78515]⟩,
        ⟨8194, false, false, [], []⟩,
        ⟨8194, false, false, [], []⟩
      ]⟩,
    ⟨[1999], [1911, 1899], .source 1064⟩,
    ⟨[2001], [1999, 1901], .source 1065⟩,
    ⟨[78561, 9], [78561, 9], .contexts []⟩,
    ⟨[78561], [78561], .contexts []⟩,
    ⟨[2003], [2000], .source 1066⟩,
    ⟨[2000], [2000], .contexts []⟩,
    ⟨[78561, 9], [2003, 78561], .contexts [
        ⟨8480, false, false, [], []⟩,
        ⟨8479, false, false, [2000], [78561, 9]⟩,
        ⟨8469, true, false, [2000, 1999], [9]⟩,
        ⟨8478, false, false, [2000], [77681, 11, 9]⟩,
        ⟨8169, true, false, [2000, 1911], [11, 9]⟩,
        ⟨8477, true, false, [2000], [9, 11, 9]⟩,
        ⟨4869, false, false, [2000, 78561], []⟩,
        ⟨8481, false, false, [2000], []⟩,
        ⟨8483, true, false, [], [78561]⟩,
        ⟨8483, true, false, [], [78561]⟩,
        ⟨8482, true, false, [], [78561]⟩
      ]⟩,
    ⟨[78561, 15], [1885, 77147], .contexts [
        ⟨8474, false, false, [], []⟩
      ]⟩,
    ⟨[2003, 78561], [2003, 78561], .contexts []⟩,
    ⟨[78561, 9], [2003, 78561], .contexts [
        ⟨8480, false, false, [], []⟩,
        ⟨8484, false, false, [], []⟩,
        ⟨8486, false, false, [], []⟩,
        ⟨8486, false, false, [], []⟩
      ]⟩,
    ⟨[2005], [2003, 1885], .source 1067⟩,
    ⟨[2007], [1887, 2005], .source 1068⟩,
    ⟨[77147, 9], [2007, 77147], .contexts [
        ⟨8471, true, false, [1884], [9]⟩,
        ⟨8471, true, false, [1884], [9]⟩,
        ⟨8470, true, false, [1884], [9]⟩,
        ⟨8485, true, false, [1884], [9]⟩,
        ⟨8472, true, false, [1884], [9]⟩,
        ⟨75, false, false, [1884, 78561], []⟩,
        ⟨78, false, false, [1884, 78561], []⟩,
        ⟨8487, false, false, [1884], [15]⟩,
        ⟨8474, false, false, [1884, 2003], []⟩,
        ⟨8488, true, false, [1884], [77147]⟩,
        ⟨8473, false, false, [1884, 2005], []⟩,
        ⟨8067, true, false, [], [2005, 77147]⟩,
        ⟨8489, true, false, [], [77147]⟩
      ]⟩,
    ⟨[77147, 9], [2007, 77147], .contexts [
        ⟨8490, false, false, [], []⟩
      ]⟩,
    ⟨[2007, 77147], [2007, 77147], .contexts []⟩,
    ⟨[2007, 77147], [2007, 77147], .contexts []⟩,
    ⟨[77147, 13], [77149], .contexts [
        ⟨473, false, false, [], []⟩
      ]⟩,
    ⟨[77149], [77149], .contexts []⟩,
    ⟨[2009], [2006], .source 1069⟩,
    ⟨[2006], [2006], .contexts []⟩,
    ⟨[77149, 15], [77151], .contexts [
        ⟨476, false, false, [], []⟩
      ]⟩,
    ⟨[77151], [77151], .contexts []⟩,
    ⟨[78563], [78561, 13], .source 39346⟩,
    ⟨[78561, 13], [78563], .contexts [
        ⟨8500, true, false, [], []⟩
      ]⟩,
    ⟨[78563, 13], [78561], .contexts [
        ⟨8501, true, false, [], [13]⟩,
        ⟨98, false, false, [78561], []⟩,
        ⟨8465, false, false, [], []⟩
      ]⟩,
    ⟨[78563], [78563], .contexts []⟩,
    ⟨[78561, 13], [78563], .contexts [
        ⟨8501, false, false, [], []⟩,
        ⟨8503, false, false, [], []⟩,
        ⟨8503, false, false, [], []⟩
      ]⟩,
    ⟨[1997, 78563], [1997, 78563], .contexts []⟩,
    ⟨[1997, 78563], [1997, 78563], .contexts []⟩,
    ⟨[78563, 1], [78563, 1], .contexts []⟩,
    ⟨[78563], [78563], .contexts []⟩,
    ⟨[78563, 1], [1997, 78563], .contexts [
        ⟨8507, false, false, [], []⟩,
        ⟨8504, true, false, [], [1]⟩,
        ⟨387, false, false, [78561], []⟩,
        ⟨390, false, false, [78561], []⟩,
        ⟨8463, false, false, [], [13, 1, 13]⟩,
        ⟨8448, false, false, [], [13, 1, 13]⟩,
        ⟨8449, false, false, [], [13, 1, 13]⟩,
        ⟨8449, false, false, [], [13, 1, 13]⟩,
        ⟨8454, false, false, [], [1, 13]⟩,
        ⟨8451, false, false, [], [1, 13]⟩,
        ⟨8452, false, false, [], [1, 13]⟩,
        ⟨8452, false, false, [], [1, 13]⟩,
        ⟨8462, false, false, [1997], [13]⟩,
        ⟨8501, false, false, [1997], []⟩,
        ⟨8505, false, false, [], []⟩,
        ⟨8506, false, false, [], []⟩,
        ⟨8508, false, false, [1997], []⟩
      ]⟩,
    ⟨[78563, 1], [1997, 78563], .contexts [
        ⟨8509, false, false, [], []⟩,
        ⟨8435, true, false, [], [78563]⟩
      ]⟩,
    ⟨[2003, 78563], [2003, 78563], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 133. -/
def y322TCContextRaw133 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2003, 78563], [2003, 78563], .contexts []⟩,
    ⟨[78563, 9], [78563, 9], .contexts []⟩,
    ⟨[2003], [2003], .contexts [
        ⟨24, false, false, [], [2003]⟩
      ]⟩,
    ⟨[2011], [1899, 1973], .source 1070⟩,
    ⟨[78563, 11], [2011, 77941], .contexts [
        ⟨8504, true, false, [], [11]⟩,
        ⟨137, false, false, [78561], []⟩,
        ⟨138, false, false, [78561], []⟩,
        ⟨8476, false, false, [], [13]⟩,
        ⟨8280, true, false, [1899, 1974], [13]⟩,
        ⟨98, false, false, [1899, 1974, 77941], []⟩,
        ⟨8278, false, true, [1899], [77941]⟩,
        ⟨8515, true, false, [], [77941]⟩,
        ⟨8288, false, false, [2011], []⟩,
        ⟨24, true, false, [], [2011, 77941]⟩
      ]⟩,
    ⟨[78565], [78563, 15], .source 39347⟩,
    ⟨[78563, 15], [78565], .contexts [
        ⟨8517, true, false, [], []⟩
      ]⟩,
    ⟨[78565, 15], [78563], .contexts [
        ⟨8518, true, false, [], [15]⟩,
        ⟨3, false, false, [78563], []⟩,
        ⟨8503, false, false, [], []⟩
      ]⟩,
    ⟨[78565], [78565], .contexts []⟩,
    ⟨[78563, 15], [78565], .contexts [
        ⟨8518, false, false, [], []⟩,
        ⟨8520, false, false, [], []⟩,
        ⟨8520, false, false, [], []⟩
      ]⟩,
    ⟨[1997, 78565], [1997, 78565], .contexts []⟩,
    ⟨[1997, 78565], [1997, 78565], .contexts []⟩,
    ⟨[78565, 1], [78565, 1], .contexts []⟩,
    ⟨[78565], [78565], .contexts []⟩,
    ⟨[78565, 1], [1997, 78565], .contexts [
        ⟨8524, false, false, [], []⟩,
        ⟨8521, true, false, [], [1]⟩,
        ⟨17, false, false, [78563], []⟩,
        ⟨21, false, false, [78563], []⟩,
        ⟨8507, false, false, [], [15]⟩,
        ⟨8510, false, false, [], [15]⟩,
        ⟨8505, false, false, [], [15]⟩,
        ⟨8506, false, false, [], [15]⟩,
        ⟨8506, false, false, [], [15]⟩,
        ⟨8518, false, false, [1997], []⟩,
        ⟨8522, false, false, [], []⟩,
        ⟨8523, false, false, [], []⟩,
        ⟨8525, false, false, [1997], []⟩,
        ⟨8435, true, false, [], [78565]⟩
      ]⟩,
    ⟨[2003, 78565], [2003, 78565], .contexts []⟩,
    ⟨[2003, 78565], [2003, 78565], .contexts []⟩,
    ⟨[2003, 78565], [2003, 78565], .contexts []⟩,
    ⟨[78565, 9], [78565, 9], .contexts []⟩,
    ⟨[78565, 9], [2003, 78565], .contexts [
        ⟨8530, false, false, [], []⟩,
        ⟨8521, true, false, [], [9]⟩,
        ⟨75, false, false, [78563], []⟩,
        ⟨78, false, false, [78563], []⟩,
        ⟨8513, false, false, [], [15]⟩,
        ⟨8513, false, false, [], [15]⟩,
        ⟨8504, true, false, [], [9, 15]⟩,
        ⟨130, false, false, [78561], [15]⟩,
        ⟨131, false, false, [78561], [15]⟩,
        ⟨8487, false, false, [], [13, 15]⟩,
        ⟨8501, false, false, [2003], [15]⟩,
        ⟨8511, false, false, [], [15]⟩,
        ⟨8512, false, false, [], [15]⟩,
        ⟨8508, false, false, [2003], [15]⟩,
        ⟨8514, true, false, [], [78563, 15]⟩,
        ⟨8511, false, false, [], [15]⟩,
        ⟨8512, false, false, [], [15]⟩,
        ⟨8512, false, false, [], [15]⟩,
        ⟨8518, false, false, [2003], []⟩,
        ⟨8527, false, false, [], []⟩,
        ⟨8528, false, false, [], []⟩,
        ⟨8529, false, false, [], []⟩
      ]⟩,
    ⟨[1885, 77151], [1885, 77151], .contexts []⟩,
    ⟨[1885, 77151], [1885, 77151], .contexts []⟩,
    ⟨[78565, 13], [78565, 13], .contexts []⟩,
    ⟨[78565, 13], [1885, 77151], .contexts [
        ⟨8534, false, false, [], []⟩,
        ⟨8521, true, false, [], [13]⟩,
        ⟨408, false, false, [78563], []⟩,
        ⟨410, false, false, [78563], []⟩,
        ⟨8502, false, false, [], [15, 13, 15]⟩,
        ⟨8464, false, false, [], [15, 13, 15]⟩,
        ⟨8465, false, false, [], [15, 13, 15]⟩,
        ⟨8465, false, false, [], [15, 13, 15]⟩,
        ⟨8485, false, false, [], [13, 15]⟩,
        ⟨8470, false, false, [], [13, 15]⟩,
        ⟨8471, false, false, [], [13, 15]⟩,
        ⟨8471, false, false, [], [13, 15]⟩,
        ⟨473, false, false, [1885], [15]⟩,
        ⟨476, false, false, [1885], []⟩,
        ⟨8532, false, false, [], []⟩,
        ⟨8533, false, false, [], []⟩,
        ⟨8499, false, false, [1885], []⟩
      ]⟩,
    ⟨[78565, 13], [1885, 77151], .contexts [
        ⟨8535, false, false, [], []⟩,
        ⟨8389, true, false, [], [77151]⟩
      ]⟩,
    ⟨[77151, 13], [1887, 78565], .contexts [
        ⟨8536, true, false, [1884], [13]⟩,
        ⟨98, false, false, [1884, 78565], []⟩,
        ⟨8067, true, false, [], [78565]⟩
      ]⟩,
    ⟨[2015], [1997, 1885], .source 1072⟩,
    ⟨[77153, 13], [77153, 13], .contexts []⟩,
    ⟨[77153], [77153], .contexts []⟩,
    ⟨[2017], [2014], .source 1073⟩,
    ⟨[2019], [2017, 1885], .source 1074⟩,
    ⟨[77153, 13], [2019, 77153], .contexts [
        ⟨8539, false, false, [], []⟩,
        ⟨479, true, false, [], [13]⟩,
        ⟨8538, false, false, [2014], [77151, 1, 13]⟩,
        ⟨8536, true, false, [2014, 1997], [1, 13]⟩,
        ⟨8523, true, false, [2014], [13, 1, 13]⟩,
        ⟨8523, true, false, [2014], [13, 1, 13]⟩,
        ⟨8522, true, false, [2014], [13, 1, 13]⟩,
        ⟨8526, true, false, [2014], [13, 1, 13]⟩,
        ⟨8524, true, false, [2014], [13, 1, 13]⟩,
        ⟨1587, false, false, [2014, 78565], []⟩,
        ⟨190, false, false, [2014, 78565], []⟩,
        ⟨8534, false, false, [2014], [1]⟩,
        ⟨8536, false, false, [2014], [1]⟩,
        ⟨8532, false, false, [2014], [1]⟩,
        ⟨8533, false, false, [2014], [1]⟩,
        ⟨8533, false, false, [2014], [1]⟩,
        ⟨479, false, false, [2014, 1885], []⟩,
        ⟨8540, false, false, [2014, 1885], []⟩,
        ⟨8541, true, false, [], [1885, 77153]⟩,
        ⟨8542, true, false, [], [77153]⟩
      ]⟩,
    ⟨[77153, 13], [2019, 77153], .contexts [
        ⟨8543, false, false, [], []⟩
      ]⟩,
    ⟨[2019, 77153], [2019, 77153], .contexts []⟩,
    ⟨[2019, 77153], [2019, 77153], .contexts []⟩,
    ⟨[77153, 13], [2019, 77153], .contexts [
        ⟨8539, false, false, [], []⟩,
        ⟨8544, false, false, [], []⟩,
        ⟨8545, false, false, [], []⟩,
        ⟨8546, false, false, [], []⟩,
        ⟨8546, false, false, [], []⟩
      ]⟩,
    ⟨[77153, 3], [77155], .contexts [
        ⟨483, false, false, [], []⟩
      ]⟩,
    ⟨[77155, 13], [77155, 13], .contexts []⟩,
    ⟨[77155], [77155], .contexts []⟩,
    ⟨[2021], [2018], .source 1075⟩,
    ⟨[2018], [2018], .contexts []⟩,
    ⟨[2021], [2018], .contexts [
        ⟨8551, false, false, [], []⟩,
        ⟨8552, false, false, [], []⟩,
        ⟨8552, false, false, [], []⟩
      ]⟩,
    ⟨[2021, 77155], [2021, 77155], .contexts []⟩,
    ⟨[77155, 13], [2021, 77155], .contexts [
        ⟨8549, false, false, [], []⟩,
        ⟨8549, false, false, [], []⟩,
        ⟨483, true, false, [], [13]⟩,
        ⟨8547, true, false, [2018], [3, 13]⟩,
        ⟨1881, false, false, [2018, 77153], []⟩,
        ⟨36, false, false, [2018, 77153], []⟩,
        ⟨8548, false, false, [2018], []⟩,
        ⟨696, false, false, [2018], []⟩,
        ⟨487, false, false, [2018], []⟩,
        ⟨487, false, false, [2018], []⟩,
        ⟨8550, false, false, [2018], []⟩,
        ⟨8553, true, false, [], [77155]⟩,
        ⟨8554, false, false, [], []⟩,
        ⟨8554, false, false, [], []⟩
      ]⟩,
    ⟨[77155, 5], [77157], .contexts [
        ⟨486, false, false, [], []⟩
      ]⟩,
    ⟨[77155, 5], [77157], .contexts [
        ⟨8556, false, false, [], []⟩,
        ⟨694, false, false, [], []⟩,
        ⟨490, false, false, [], []⟩,
        ⟨490, false, false, [], []⟩
      ]⟩,
    ⟨[77157, 13], [77157, 13], .contexts []⟩,
    ⟨[77157], [77157], .contexts []⟩,
    ⟨[2020], [2020], .contexts []⟩,
    ⟨[77157, 13], [2019, 77157], .contexts [
        ⟨8558, false, false, [], []⟩,
        ⟨486, true, false, [], [13]⟩,
        ⟨8555, true, false, [2020], [5, 13]⟩,
        ⟨1886, false, false, [2020, 77155], []⟩,
        ⟨50, false, false, [2020, 77155], []⟩,
        ⟨8557, false, false, [2020], []⟩,
        ⟨8559, false, false, [2020], []⟩,
        ⟨8560, true, false, [], [77157]⟩,
        ⟨8560, true, false, [], [77157]⟩,
        ⟨8551, false, true, [], [77157]⟩
      ]⟩,
    ⟨[78567], [78565, 3], .source 39348⟩,
    ⟨[78565, 3], [78567], .contexts [
        ⟨8562, true, false, [], []⟩
      ]⟩,
    ⟨[78567], [78567], .contexts []⟩,
    ⟨[2003, 78567], [2003, 78567], .contexts []⟩,
    ⟨[2003, 78567], [2003, 78567], .contexts []⟩,
    ⟨[2003, 78567], [2003, 78567], .contexts []⟩,
    ⟨[78567, 9], [78567, 9], .contexts []⟩,
    ⟨[78569], [78567, 5], .source 39349⟩,
    ⟨[78567, 5], [78569], .contexts [
        ⟨8569, true, false, [], []⟩
      ]⟩,
    ⟨[78569], [78569], .contexts []⟩,
    ⟨[78569], [78569], .contexts []⟩,
    ⟨[78567, 9, 5], [2003, 78567, 5], .contexts [
        ⟨8568, false, false, [], [5]⟩,
        ⟨8568, false, false, [], [5]⟩,
        ⟨8564, true, false, [], [9, 5]⟩,
        ⟨8564, true, false, [], [9, 5]⟩,
        ⟨8563, true, false, [], [9, 5]⟩,
        ⟨1112, false, false, [78565], [5]⟩,
        ⟨1113, false, false, [78565], [5]⟩,
        ⟨8530, false, false, [], [3, 5]⟩,
        ⟨8531, false, false, [], [3, 5]⟩,
        ⟨8525, false, false, [2003], [3, 5]⟩,
        ⟨8514, true, false, [], [78565, 3, 5]⟩,
        ⟨8527, false, false, [], [3, 5]⟩,
        ⟨8529, false, false, [], [3, 5]⟩,
        ⟨8529, false, false, [], [3, 5]⟩,
        ⟨8563, false, false, [2003], [5]⟩,
        ⟨8565, false, false, [], [5]⟩,
        ⟨8566, false, false, [], [5]⟩,
        ⟨8567, false, false, [], [5]⟩,
        ⟨8514, true, false, [], [78567, 5]⟩,
        ⟨8565, false, false, [], [5]⟩,
        ⟨8567, false, false, [], [5]⟩,
        ⟨8567, false, false, [], [5]⟩
      ]⟩,
    ⟨[2003, 78569], [2003, 78569], .contexts []⟩,
    ⟨[2003, 78569], [2003, 78569], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 134. -/
def y322TCContextRaw134 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2003, 78569], [2003, 78569], .contexts []⟩,
    ⟨[78571], [78569, 1], .source 39350⟩,
    ⟨[78569, 1], [78571], .contexts [
        ⟨8577, true, false, [], []⟩
      ]⟩,
    ⟨[78571, 1], [78569], .contexts [
        ⟨8578, true, false, [], [1]⟩,
        ⟨18, false, false, [78569], []⟩,
        ⟨8572, false, false, [], []⟩
      ]⟩,
    ⟨[78573], [78571, 9], .source 39351⟩,
    ⟨[78571, 9], [78573], .contexts [
        ⟨8580, true, false, [], []⟩
      ]⟩,
    ⟨[78573], [78573], .contexts []⟩,
    ⟨[2003, 78571], [2003, 78571], .contexts []⟩,
    ⟨[2003, 78571], [2003, 78571], .contexts []⟩,
    ⟨[2003, 78571], [2003, 78571], .contexts []⟩,
    ⟨[78571, 1, 9, 1], [2003, 78571], .contexts [
        ⟨8579, false, false, [], [9, 1]⟩,
        ⟨8571, false, false, [], [9, 1]⟩,
        ⟨8572, false, false, [], [9, 1]⟩,
        ⟨8572, false, false, [], [9, 1]⟩,
        ⟨8572, true, false, [], [9, 1]⟩,
        ⟨8572, true, false, [], [9, 1]⟩,
        ⟨8571, true, false, [], [9, 1]⟩,
        ⟨8570, true, false, [], [9, 1]⟩,
        ⟨2076, false, false, [78567], [1]⟩,
        ⟨2077, false, false, [78567], [1]⟩,
        ⟨8573, false, false, [], [1]⟩,
        ⟨8570, false, false, [2003], [1]⟩,
        ⟨8574, false, false, [], [1]⟩,
        ⟨8575, false, false, [], [1]⟩,
        ⟨8576, false, false, [], [1]⟩,
        ⟨8514, true, false, [], [78569, 1]⟩,
        ⟨8574, false, false, [], [1]⟩,
        ⟨8576, false, false, [], [1]⟩,
        ⟨8576, false, false, [], [1]⟩,
        ⟨8578, false, false, [2003], []⟩,
        ⟨8583, false, false, [], []⟩,
        ⟨8584, false, false, [], []⟩,
        ⟨8585, false, false, [], []⟩
      ]⟩,
    ⟨[2003, 78573], [2003, 78573], .contexts []⟩,
    ⟨[2003, 78573], [2003, 78573], .contexts []⟩,
    ⟨[2003, 78573], [2003, 78573], .contexts []⟩,
    ⟨[78573, 1], [78573, 1], .contexts []⟩,
    ⟨[78575], [78573, 11], .source 39352⟩,
    ⟨[78573, 11], [78575], .contexts [
        ⟨8591, true, false, [], []⟩
      ]⟩,
    ⟨[78575], [78575], .contexts []⟩,
    ⟨[78575], [78575], .contexts []⟩,
    ⟨[2003, 78575], [2003, 78575], .contexts []⟩,
    ⟨[2003, 78575], [2003, 78575], .contexts []⟩,
    ⟨[78573, 1, 11], [2003, 78575], .contexts [
        ⟨8590, false, false, [], [11]⟩,
        ⟨8590, false, false, [], [11]⟩,
        ⟨8582, true, false, [], [1, 11]⟩,
        ⟨8582, true, false, [], [1, 11]⟩,
        ⟨8581, true, false, [], [1, 11]⟩,
        ⟨1143, false, false, [78571], [11]⟩,
        ⟨1146, false, false, [78571], [11]⟩,
        ⟨8586, false, false, [], [9, 11]⟩,
        ⟨8581, false, false, [2003], [11]⟩,
        ⟨8587, false, false, [], [11]⟩,
        ⟨8588, false, false, [], [11]⟩,
        ⟨8589, false, false, [], [11]⟩,
        ⟨8514, true, false, [], [78573, 11]⟩,
        ⟨8587, false, false, [], [11]⟩,
        ⟨8589, false, false, [], [11]⟩,
        ⟨8589, false, false, [], [11]⟩,
        ⟨8592, false, false, [2003], []⟩,
        ⟨8595, false, false, [], []⟩,
        ⟨8596, false, false, [], []⟩
      ]⟩,
    ⟨[78577], [78575, 13], .source 39353⟩,
    ⟨[78579], [78577, 15], .source 39354⟩,
    ⟨[78577], [78577], .contexts []⟩,
    ⟨[78581], [78579, 1], .source 39355⟩,
    ⟨[78579], [78579], .contexts []⟩,
    ⟨[78583], [78581, 3], .source 39356⟩,
    ⟨[78581], [78581], .contexts []⟩,
    ⟨[78585], [78583, 5], .source 39357⟩,
    ⟨[78583], [78583], .contexts []⟩,
    ⟨[78587], [78585, 1], .source 39358⟩,
    ⟨[78585], [78585], .contexts []⟩,
    ⟨[78589], [78587, 9], .source 39359⟩,
    ⟨[78587], [78587], .contexts []⟩,
    ⟨[78591], [78589, 11], .source 39360⟩,
    ⟨[78589], [78589], .contexts []⟩,
    ⟨[78593], [78591, 1], .source 39361⟩,
    ⟨[78591], [78591], .contexts []⟩,
    ⟨[78595], [78593, 13], .source 39362⟩,
    ⟨[78593], [78593], .contexts []⟩,
    ⟨[78597], [78595, 15], .source 39363⟩,
    ⟨[78595], [78595], .contexts []⟩,
    ⟨[78599], [78597, 1], .source 39364⟩,
    ⟨[78597], [78597], .contexts []⟩,
    ⟨[78601], [78599, 3], .source 39365⟩,
    ⟨[78599], [78599], .contexts []⟩,
    ⟨[78603], [78601, 5], .source 39366⟩,
    ⟨[78601], [78601], .contexts []⟩,
    ⟨[78605], [78603, 1], .source 39367⟩,
    ⟨[78603], [78603], .contexts []⟩,
    ⟨[78607], [78605, 9], .source 39368⟩,
    ⟨[78605], [78605], .contexts []⟩,
    ⟨[78609], [78607, 11], .source 39369⟩,
    ⟨[78607], [78607], .contexts []⟩,
    ⟨[78611], [78609, 1], .source 39370⟩,
    ⟨[78609], [78609], .contexts []⟩,
    ⟨[78613], [78611, 13], .source 39371⟩,
    ⟨[78611, 13], [78613], .contexts [
        ⟨8633, true, false, [], []⟩
      ]⟩,
    ⟨[78611], [78611], .contexts []⟩,
    ⟨[78613, 13], [78611], .contexts [
        ⟨8634, true, false, [], [13]⟩,
        ⟨98, false, false, [78611], []⟩,
        ⟨8635, false, false, [], []⟩
      ]⟩,
    ⟨[78615], [78613, 15], .source 39372⟩,
    ⟨[78613, 15], [78615], .contexts [
        ⟨8637, true, false, [], []⟩
      ]⟩,
    ⟨[78613], [78613], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 135. -/
def y322TCContextRaw135 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78615, 15], [78613], .contexts [
        ⟨8638, true, false, [], [15]⟩,
        ⟨3, false, false, [78613], []⟩,
        ⟨8639, false, false, [], []⟩
      ]⟩,
    ⟨[78617], [78615, 1], .source 39373⟩,
    ⟨[78615, 1], [78617], .contexts [
        ⟨8641, true, false, [], []⟩
      ]⟩,
    ⟨[78615], [78615], .contexts []⟩,
    ⟨[78617, 1], [78615], .contexts [
        ⟨8642, true, false, [], [1]⟩,
        ⟨18, false, false, [78615], []⟩,
        ⟨8643, false, false, [], []⟩
      ]⟩,
    ⟨[78619], [78617, 3], .source 39374⟩,
    ⟨[78617], [78617], .contexts []⟩,
    ⟨[78619, 3], [78617], .contexts [
        ⟨8645, false, false, [], [3]⟩,
        ⟨35, false, false, [78617], []⟩,
        ⟨8646, false, false, [], []⟩
      ]⟩,
    ⟨[78621], [78619, 5], .source 39375⟩,
    ⟨[78619], [78619], .contexts []⟩,
    ⟨[78621, 5], [78619], .contexts [
        ⟨8648, false, false, [], [5]⟩,
        ⟨49, false, false, [78619], []⟩,
        ⟨8649, false, false, [], []⟩
      ]⟩,
    ⟨[78623], [78621, 1], .source 39376⟩,
    ⟨[78621], [78621], .contexts []⟩,
    ⟨[78623, 1], [78621], .contexts [
        ⟨8651, false, false, [], [1]⟩,
        ⟨18, false, false, [78621], []⟩,
        ⟨8652, false, false, [], []⟩
      ]⟩,
    ⟨[78625], [78623, 9], .source 39377⟩,
    ⟨[78623, 9], [78625], .contexts [
        ⟨8654, true, false, [], []⟩
      ]⟩,
    ⟨[78623], [78623], .contexts []⟩,
    ⟨[78625, 9], [78623], .contexts [
        ⟨8655, true, false, [], [9]⟩,
        ⟨76, false, false, [78623], []⟩,
        ⟨8656, false, false, [], []⟩
      ]⟩,
    ⟨[78627], [78625, 11], .source 39378⟩,
    ⟨[78625, 11], [78627], .contexts [
        ⟨8658, true, false, [], []⟩
      ]⟩,
    ⟨[78625], [78625], .contexts []⟩,
    ⟨[78627, 11], [78625], .contexts [
        ⟨8659, true, false, [], [11]⟩,
        ⟨90, false, false, [78625], []⟩,
        ⟨8660, false, false, [], []⟩
      ]⟩,
    ⟨[78629], [78627, 1], .source 39379⟩,
    ⟨[78627, 1], [78629], .contexts [
        ⟨8662, true, false, [], []⟩
      ]⟩,
    ⟨[78627], [78627], .contexts []⟩,
    ⟨[78629, 1], [78627], .contexts [
        ⟨8663, true, false, [], [1]⟩,
        ⟨18, false, false, [78627], []⟩,
        ⟨8664, false, false, [], []⟩
      ]⟩,
    ⟨[78631], [78629, 13], .source 39380⟩,
    ⟨[78629, 13], [78631], .contexts [
        ⟨8666, true, false, [], []⟩
      ]⟩,
    ⟨[78629], [78629], .contexts []⟩,
    ⟨[78631, 13], [78629], .contexts [
        ⟨8667, true, false, [], [13]⟩,
        ⟨98, false, false, [78629], []⟩,
        ⟨8668, false, false, [], []⟩
      ]⟩,
    ⟨[78633], [78631, 15], .source 39381⟩,
    ⟨[78631, 15], [78633], .contexts [
        ⟨8670, true, false, [], []⟩
      ]⟩,
    ⟨[78631], [78631], .contexts []⟩,
    ⟨[78633, 15], [78631], .contexts [
        ⟨8671, true, false, [], [15]⟩,
        ⟨3, false, false, [78631], []⟩,
        ⟨8672, false, false, [], []⟩
      ]⟩,
    ⟨[78635], [78633, 1], .source 39382⟩,
    ⟨[78633, 1], [78635], .contexts [
        ⟨8674, true, false, [], []⟩
      ]⟩,
    ⟨[78633], [78633], .contexts []⟩,
    ⟨[78635, 1], [78633], .contexts [
        ⟨8675, true, false, [], [1]⟩,
        ⟨18, false, false, [78633], []⟩,
        ⟨8676, false, false, [], []⟩
      ]⟩,
    ⟨[78637], [78635, 3], .source 39383⟩,
    ⟨[78635, 3], [78637], .contexts [
        ⟨8678, true, false, [], []⟩
      ]⟩,
    ⟨[78635], [78635], .contexts []⟩,
    ⟨[78637, 3], [78635], .contexts [
        ⟨8679, true, false, [], [3]⟩,
        ⟨35, false, false, [78635], []⟩,
        ⟨8680, false, false, [], []⟩
      ]⟩,
    ⟨[78639], [78637, 5], .source 39384⟩,
    ⟨[78637, 5], [78639], .contexts [
        ⟨8682, true, false, [], []⟩
      ]⟩,
    ⟨[78637], [78637], .contexts []⟩,
    ⟨[78639, 5], [78637], .contexts [
        ⟨8683, true, false, [], [5]⟩,
        ⟨49, false, false, [78637], []⟩,
        ⟨8684, false, false, [], []⟩
      ]⟩,
    ⟨[78641], [78639, 1], .source 39385⟩,
    ⟨[78639], [78639], .contexts []⟩,
    ⟨[78641, 1], [78639], .contexts [
        ⟨8686, false, false, [], [1]⟩,
        ⟨18, false, false, [78639], []⟩,
        ⟨8687, false, false, [], []⟩
      ]⟩,
    ⟨[78643], [78641, 9], .source 39386⟩,
    ⟨[78641], [78641], .contexts []⟩,
    ⟨[78643, 9], [78641], .contexts [
        ⟨8689, false, false, [], [9]⟩,
        ⟨76, false, false, [78641], []⟩,
        ⟨8690, false, false, [], []⟩
      ]⟩,
    ⟨[78645], [78643, 11], .source 39387⟩,
    ⟨[78643], [78643], .contexts []⟩,
    ⟨[78645, 11], [78643], .contexts [
        ⟨8692, false, false, [], [11]⟩,
        ⟨90, false, false, [78643], []⟩,
        ⟨8693, false, false, [], []⟩
      ]⟩,
    ⟨[78647], [78645, 1], .source 39388⟩,
    ⟨[78645], [78645], .contexts []⟩,
    ⟨[78647, 1], [78645], .contexts [
        ⟨8695, false, false, [], [1]⟩,
        ⟨18, false, false, [78645], []⟩,
        ⟨8696, false, false, [], []⟩
      ]⟩,
    ⟨[78649], [78647, 13], .source 39389⟩,
    ⟨[78647], [78647], .contexts []⟩,
    ⟨[78649, 13], [78647], .contexts [
        ⟨8698, false, false, [], [13]⟩,
        ⟨98, false, false, [78647], []⟩,
        ⟨8699, false, false, [], []⟩
      ]⟩,
    ⟨[78651], [78649, 15], .source 39390⟩,
    ⟨[78649], [78649], .contexts []⟩,
    ⟨[78651, 15], [78649], .contexts [
        ⟨8701, false, false, [], [15]⟩,
        ⟨3, false, false, [78649], []⟩,
        ⟨8702, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 136. -/
def y322TCContextRaw136 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78653], [78651, 1], .source 39391⟩,
    ⟨[78651], [78651], .contexts []⟩,
    ⟨[78653, 1], [78651], .contexts [
        ⟨8704, false, false, [], [1]⟩,
        ⟨18, false, false, [78651], []⟩,
        ⟨8705, false, false, [], []⟩
      ]⟩,
    ⟨[78655], [78653, 3], .source 39392⟩,
    ⟨[78653], [78653], .contexts []⟩,
    ⟨[78655, 3], [78653], .contexts [
        ⟨8707, false, false, [], [3]⟩,
        ⟨35, false, false, [78653], []⟩,
        ⟨8708, false, false, [], []⟩
      ]⟩,
    ⟨[78657], [78655, 5], .source 39393⟩,
    ⟨[78655], [78655], .contexts []⟩,
    ⟨[78657, 5], [78655], .contexts [
        ⟨8710, false, false, [], [5]⟩,
        ⟨49, false, false, [78655], []⟩,
        ⟨8711, false, false, [], []⟩
      ]⟩,
    ⟨[78659], [78657, 1], .source 39394⟩,
    ⟨[78657], [78657], .contexts []⟩,
    ⟨[78659, 1], [78657], .contexts [
        ⟨8713, false, false, [], [1]⟩,
        ⟨18, false, false, [78657], []⟩,
        ⟨8714, false, false, [], []⟩
      ]⟩,
    ⟨[78661], [78659, 9], .source 39395⟩,
    ⟨[78659], [78659], .contexts []⟩,
    ⟨[78661, 9], [78659], .contexts [
        ⟨8716, false, false, [], [9]⟩,
        ⟨76, false, false, [78659], []⟩,
        ⟨8717, false, false, [], []⟩
      ]⟩,
    ⟨[78663], [78661, 11], .source 39396⟩,
    ⟨[78661], [78661], .contexts []⟩,
    ⟨[78663, 11], [78661], .contexts [
        ⟨8719, false, false, [], [11]⟩,
        ⟨90, false, false, [78661], []⟩,
        ⟨8720, false, false, [], []⟩
      ]⟩,
    ⟨[78665], [78663, 1], .source 39397⟩,
    ⟨[78663], [78663], .contexts []⟩,
    ⟨[78665, 1], [78663], .contexts [
        ⟨8722, false, false, [], [1]⟩,
        ⟨18, false, false, [78663], []⟩,
        ⟨8723, false, false, [], []⟩
      ]⟩,
    ⟨[78667], [78665, 13], .source 39398⟩,
    ⟨[78665], [78665], .contexts []⟩,
    ⟨[78667, 13], [78665], .contexts [
        ⟨8725, false, false, [], [13]⟩,
        ⟨98, false, false, [78665], []⟩,
        ⟨8726, false, false, [], []⟩
      ]⟩,
    ⟨[78669], [78667, 15], .source 39399⟩,
    ⟨[78667], [78667], .contexts []⟩,
    ⟨[78669, 15], [78667], .contexts [
        ⟨8728, false, false, [], [15]⟩,
        ⟨3, false, false, [78667], []⟩,
        ⟨8729, false, false, [], []⟩
      ]⟩,
    ⟨[78671], [78669, 1], .source 39400⟩,
    ⟨[78669], [78669], .contexts []⟩,
    ⟨[78671, 1], [78669], .contexts [
        ⟨8731, false, false, [], [1]⟩,
        ⟨18, false, false, [78669], []⟩,
        ⟨8732, false, false, [], []⟩
      ]⟩,
    ⟨[78673], [78671, 3], .source 39401⟩,
    ⟨[78671], [78671], .contexts []⟩,
    ⟨[78673, 3], [78671], .contexts [
        ⟨8734, false, false, [], [3]⟩,
        ⟨35, false, false, [78671], []⟩,
        ⟨8735, false, false, [], []⟩
      ]⟩,
    ⟨[78675], [78673, 5], .source 39402⟩,
    ⟨[78673], [78673], .contexts []⟩,
    ⟨[78675, 5], [78673], .contexts [
        ⟨8737, false, false, [], [5]⟩,
        ⟨49, false, false, [78673], []⟩,
        ⟨8738, false, false, [], []⟩
      ]⟩,
    ⟨[78677], [78675, 1], .source 39403⟩,
    ⟨[78675], [78675], .contexts []⟩,
    ⟨[78677, 1], [78675], .contexts [
        ⟨8740, false, false, [], [1]⟩,
        ⟨18, false, false, [78675], []⟩,
        ⟨8741, false, false, [], []⟩
      ]⟩,
    ⟨[78679], [78677, 9], .source 39404⟩,
    ⟨[78677], [78677], .contexts []⟩,
    ⟨[78679, 9], [78677], .contexts [
        ⟨8743, false, false, [], [9]⟩,
        ⟨76, false, false, [78677], []⟩,
        ⟨8744, false, false, [], []⟩
      ]⟩,
    ⟨[78681], [78679, 11], .source 39405⟩,
    ⟨[78679], [78679], .contexts []⟩,
    ⟨[78681, 11], [78679], .contexts [
        ⟨8746, false, false, [], [11]⟩,
        ⟨90, false, false, [78679], []⟩,
        ⟨8747, false, false, [], []⟩
      ]⟩,
    ⟨[78683], [78681, 1], .source 39406⟩,
    ⟨[78681], [78681], .contexts []⟩,
    ⟨[78683, 1], [78681], .contexts [
        ⟨8749, false, false, [], [1]⟩,
        ⟨18, false, false, [78681], []⟩,
        ⟨8750, false, false, [], []⟩
      ]⟩,
    ⟨[78685], [78683, 13], .source 39407⟩,
    ⟨[78683], [78683], .contexts []⟩,
    ⟨[78685, 13], [78683], .contexts [
        ⟨8752, false, false, [], [13]⟩,
        ⟨98, false, false, [78683], []⟩,
        ⟨8753, false, false, [], []⟩
      ]⟩,
    ⟨[78687], [78685, 15], .source 39408⟩,
    ⟨[78685], [78685], .contexts []⟩,
    ⟨[78687, 15], [78685], .contexts [
        ⟨8755, false, false, [], [15]⟩,
        ⟨3, false, false, [78685], []⟩,
        ⟨8756, false, false, [], []⟩
      ]⟩,
    ⟨[78689], [78687, 1], .source 39409⟩,
    ⟨[78687], [78687], .contexts []⟩,
    ⟨[78689, 1], [78687], .contexts [
        ⟨8758, false, false, [], [1]⟩,
        ⟨18, false, false, [78687], []⟩,
        ⟨8759, false, false, [], []⟩
      ]⟩,
    ⟨[78691], [78689, 3], .source 39410⟩,
    ⟨[78689], [78689], .contexts []⟩,
    ⟨[78691, 3], [78689], .contexts [
        ⟨8761, false, false, [], [3]⟩,
        ⟨35, false, false, [78689], []⟩,
        ⟨8762, false, false, [], []⟩
      ]⟩,
    ⟨[78693], [78691, 5], .source 39411⟩,
    ⟨[78691], [78691], .contexts []⟩,
    ⟨[78693, 5], [78691], .contexts [
        ⟨8764, false, false, [], [5]⟩,
        ⟨49, false, false, [78691], []⟩,
        ⟨8765, false, false, [], []⟩
      ]⟩,
    ⟨[78695], [78693, 1], .source 39412⟩]

/-- Exact literal claimed equations and contextual derivations, block 137. -/
def y322TCContextRaw137 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78693], [78693], .contexts []⟩,
    ⟨[78695, 1], [78693], .contexts [
        ⟨8767, false, false, [], [1]⟩,
        ⟨18, false, false, [78693], []⟩,
        ⟨8768, false, false, [], []⟩
      ]⟩,
    ⟨[78697], [78695, 9], .source 39413⟩,
    ⟨[78695], [78695], .contexts []⟩,
    ⟨[78697, 9], [78695], .contexts [
        ⟨8770, false, false, [], [9]⟩,
        ⟨76, false, false, [78695], []⟩,
        ⟨8771, false, false, [], []⟩
      ]⟩,
    ⟨[78699], [78697, 11], .source 39414⟩,
    ⟨[78697], [78697], .contexts []⟩,
    ⟨[78699, 11], [78697], .contexts [
        ⟨8773, false, false, [], [11]⟩,
        ⟨90, false, false, [78697], []⟩,
        ⟨8774, false, false, [], []⟩
      ]⟩,
    ⟨[78701], [78699, 1], .source 39415⟩,
    ⟨[78699], [78699], .contexts []⟩,
    ⟨[78701, 1], [78699], .contexts [
        ⟨8776, false, false, [], [1]⟩,
        ⟨18, false, false, [78699], []⟩,
        ⟨8777, false, false, [], []⟩
      ]⟩,
    ⟨[78703], [78701, 13], .source 39416⟩,
    ⟨[78701], [78701], .contexts []⟩,
    ⟨[78703, 13], [78701], .contexts [
        ⟨8779, false, false, [], [13]⟩,
        ⟨98, false, false, [78701], []⟩,
        ⟨8780, false, false, [], []⟩
      ]⟩,
    ⟨[78705], [78703, 15], .source 39417⟩,
    ⟨[78703], [78703], .contexts []⟩,
    ⟨[78705, 15], [78703], .contexts [
        ⟨8782, false, false, [], [15]⟩,
        ⟨3, false, false, [78703], []⟩,
        ⟨8783, false, false, [], []⟩
      ]⟩,
    ⟨[78707], [78705, 1], .source 39418⟩,
    ⟨[78705], [78705], .contexts []⟩,
    ⟨[78707, 1], [78705], .contexts [
        ⟨8785, false, false, [], [1]⟩,
        ⟨18, false, false, [78705], []⟩,
        ⟨8786, false, false, [], []⟩
      ]⟩,
    ⟨[78709], [78707, 3], .source 39419⟩,
    ⟨[78707], [78707], .contexts []⟩,
    ⟨[78709, 3], [78707], .contexts [
        ⟨8788, false, false, [], [3]⟩,
        ⟨35, false, false, [78707], []⟩,
        ⟨8789, false, false, [], []⟩
      ]⟩,
    ⟨[78711], [78709, 5], .source 39420⟩,
    ⟨[78709], [78709], .contexts []⟩,
    ⟨[78711, 5], [78709], .contexts [
        ⟨8791, false, false, [], [5]⟩,
        ⟨49, false, false, [78709], []⟩,
        ⟨8792, false, false, [], []⟩
      ]⟩,
    ⟨[78713], [78711, 1], .source 39421⟩,
    ⟨[78711], [78711], .contexts []⟩,
    ⟨[78713, 1], [78711], .contexts [
        ⟨8794, false, false, [], [1]⟩,
        ⟨18, false, false, [78711], []⟩,
        ⟨8795, false, false, [], []⟩
      ]⟩,
    ⟨[78715], [78713, 9], .source 39422⟩,
    ⟨[78713, 9], [78715], .contexts [
        ⟨8797, true, false, [], []⟩
      ]⟩,
    ⟨[78715, 9], [78713], .contexts [
        ⟨8798, true, false, [], [9]⟩,
        ⟨76, false, false, [78713], []⟩
      ]⟩,
    ⟨[78715], [78715], .contexts []⟩,
    ⟨[78711], [78711], .contexts []⟩,
    ⟨[78709], [78709], .contexts []⟩,
    ⟨[78707], [78707], .contexts []⟩,
    ⟨[78705], [78705], .contexts []⟩,
    ⟨[78703], [78703], .contexts []⟩,
    ⟨[78713, 1, 5, 3, 1, 15], [78703], .contexts [
        ⟨8796, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8801, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8795, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8795, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8793, false, false, [], [3, 1, 15]⟩,
        ⟨8802, false, false, [], [3, 1, 15]⟩,
        ⟨8792, false, false, [], [3, 1, 15]⟩,
        ⟨8792, false, false, [], [3, 1, 15]⟩,
        ⟨8790, false, false, [], [1, 15]⟩,
        ⟨8803, false, false, [], [1, 15]⟩,
        ⟨8789, false, false, [], [1, 15]⟩,
        ⟨8789, false, false, [], [1, 15]⟩,
        ⟨8787, false, false, [], [15]⟩,
        ⟨8804, false, false, [], [15]⟩,
        ⟨8786, false, false, [], [15]⟩,
        ⟨8786, false, false, [], [15]⟩,
        ⟨8784, false, false, [], []⟩,
        ⟨8805, false, false, [], []⟩,
        ⟨8783, false, false, [], []⟩,
        ⟨8783, false, false, [], []⟩
      ]⟩,
    ⟨[78701], [78701], .contexts []⟩,
    ⟨[78699], [78699], .contexts []⟩,
    ⟨[78697], [78697], .contexts []⟩,
    ⟨[78695], [78695], .contexts []⟩,
    ⟨[78693], [78693], .contexts []⟩,
    ⟨[78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [78693], .contexts [
        ⟨8806, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨8781, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8807, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8780, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8780, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8778, false, false, [], [11, 9, 1]⟩,
        ⟨8808, false, false, [], [11, 9, 1]⟩,
        ⟨8777, false, false, [], [11, 9, 1]⟩,
        ⟨8777, false, false, [], [11, 9, 1]⟩,
        ⟨8775, false, false, [], [9, 1]⟩,
        ⟨8809, false, false, [], [9, 1]⟩,
        ⟨8774, false, false, [], [9, 1]⟩,
        ⟨8774, false, false, [], [9, 1]⟩,
        ⟨8772, false, false, [], [1]⟩,
        ⟨8810, false, false, [], [1]⟩,
        ⟨8771, false, false, [], [1]⟩,
        ⟨8771, false, false, [], [1]⟩,
        ⟨8769, false, false, [], []⟩,
        ⟨8811, false, false, [], []⟩,
        ⟨8768, false, false, [], []⟩,
        ⟨8768, false, false, [], []⟩
      ]⟩,
    ⟨[78691], [78691], .contexts []⟩,
    ⟨[78689], [78689], .contexts []⟩,
    ⟨[78687], [78687], .contexts []⟩,
    ⟨[78685], [78685], .contexts []⟩,
    ⟨[78683], [78683], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13
    ], [78683], .contexts [
        ⟨8812, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨8766, false, false, [], [3, 1, 15, 13]⟩,
        ⟨8813, false, false, [], [3, 1, 15, 13]⟩,
        ⟨8765, false, false, [], [3, 1, 15, 13]⟩,
        ⟨8765, false, false, [], [3, 1, 15, 13]⟩,
        ⟨8763, false, false, [], [1, 15, 13]⟩,
        ⟨8814, false, false, [], [1, 15, 13]⟩,
        ⟨8762, false, false, [], [1, 15, 13]⟩,
        ⟨8762, false, false, [], [1, 15, 13]⟩,
        ⟨8760, false, false, [], [15, 13]⟩,
        ⟨8815, false, false, [], [15, 13]⟩,
        ⟨8759, false, false, [], [15, 13]⟩,
        ⟨8759, false, false, [], [15, 13]⟩,
        ⟨8757, false, false, [], [13]⟩,
        ⟨8816, false, false, [], [13]⟩,
        ⟨8756, false, false, [], [13]⟩,
        ⟨8756, false, false, [], [13]⟩,
        ⟨8754, false, false, [], []⟩,
        ⟨8817, false, false, [], []⟩,
        ⟨8753, false, false, [], []⟩,
        ⟨8753, false, false, [], []⟩
      ]⟩,
    ⟨[78681], [78681], .contexts []⟩,
    ⟨[78679], [78679], .contexts []⟩,
    ⟨[78677], [78677], .contexts []⟩,
    ⟨[78675], [78675], .contexts []⟩,
    ⟨[78673], [78673], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [78673], .contexts [
        ⟨8818, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨8751, false, false, [], [11, 9, 1, 5]⟩,
        ⟨8819, false, false, [], [11, 9, 1, 5]⟩,
        ⟨8750, false, false, [], [11, 9, 1, 5]⟩,
        ⟨8750, false, false, [], [11, 9, 1, 5]⟩,
        ⟨8748, false, false, [], [9, 1, 5]⟩,
        ⟨8820, false, false, [], [9, 1, 5]⟩,
        ⟨8747, false, false, [], [9, 1, 5]⟩,
        ⟨8747, false, false, [], [9, 1, 5]⟩,
        ⟨8745, false, false, [], [1, 5]⟩,
        ⟨8821, false, false, [], [1, 5]⟩,
        ⟨8744, false, false, [], [1, 5]⟩,
        ⟨8744, false, false, [], [1, 5]⟩,
        ⟨8742, false, false, [], [5]⟩,
        ⟨8822, false, false, [], [5]⟩,
        ⟨8741, false, false, [], [5]⟩,
        ⟨8741, false, false, [], [5]⟩,
        ⟨8739, false, false, [], []⟩,
        ⟨8823, false, false, [], []⟩,
        ⟨8738, false, false, [], []⟩,
        ⟨8738, false, false, [], []⟩
      ]⟩,
    ⟨[78671], [78671], .contexts []⟩,
    ⟨[78669], [78669], .contexts []⟩,
    ⟨[78667], [78667], .contexts []⟩,
    ⟨[78665], [78665], .contexts []⟩,
    ⟨[78663], [78663], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1
    ], [78663], .contexts [
        ⟨8824, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨8736, false, false, [], [1, 15, 13, 1]⟩,
        ⟨8825, false, false, [], [1, 15, 13, 1]⟩,
        ⟨8735, false, false, [], [1, 15, 13, 1]⟩,
        ⟨8735, false, false, [], [1, 15, 13, 1]⟩,
        ⟨8733, false, false, [], [15, 13, 1]⟩,
        ⟨8826, false, false, [], [15, 13, 1]⟩,
        ⟨8732, false, false, [], [15, 13, 1]⟩,
        ⟨8732, false, false, [], [15, 13, 1]⟩,
        ⟨8730, false, false, [], [13, 1]⟩,
        ⟨8827, false, false, [], [13, 1]⟩,
        ⟨8729, false, false, [], [13, 1]⟩,
        ⟨8729, false, false, [], [13, 1]⟩,
        ⟨8727, false, false, [], [1]⟩,
        ⟨8828, false, false, [], [1]⟩,
        ⟨8726, false, false, [], [1]⟩,
        ⟨8726, false, false, [], [1]⟩,
        ⟨8724, false, false, [], []⟩,
        ⟨8829, false, false, [], []⟩,
        ⟨8723, false, false, [], []⟩,
        ⟨8723, false, false, [], []⟩
      ]⟩,
    ⟨[78661], [78661], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 138. -/
def y322TCContextRaw138 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78659], [78659], .contexts []⟩,
    ⟨[78657], [78657], .contexts []⟩,
    ⟨[78655], [78655], .contexts []⟩,
    ⟨[78653], [78653], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3
    ], [78653], .contexts [
        ⟨8830, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨8721, false, false, [], [9, 1, 5, 3]⟩,
        ⟨8831, false, false, [], [9, 1, 5, 3]⟩,
        ⟨8720, false, false, [], [9, 1, 5, 3]⟩,
        ⟨8720, false, false, [], [9, 1, 5, 3]⟩,
        ⟨8718, false, false, [], [1, 5, 3]⟩,
        ⟨8832, false, false, [], [1, 5, 3]⟩,
        ⟨8717, false, false, [], [1, 5, 3]⟩,
        ⟨8717, false, false, [], [1, 5, 3]⟩,
        ⟨8715, false, false, [], [5, 3]⟩,
        ⟨8833, false, false, [], [5, 3]⟩,
        ⟨8714, false, false, [], [5, 3]⟩,
        ⟨8714, false, false, [], [5, 3]⟩,
        ⟨8712, false, false, [], [3]⟩,
        ⟨8834, false, false, [], [3]⟩,
        ⟨8711, false, false, [], [3]⟩,
        ⟨8711, false, false, [], [3]⟩,
        ⟨8709, false, false, [], []⟩,
        ⟨8835, false, false, [], []⟩,
        ⟨8708, false, false, [], []⟩,
        ⟨8708, false, false, [], []⟩
      ]⟩,
    ⟨[78651], [78651], .contexts []⟩,
    ⟨[78649], [78649], .contexts []⟩,
    ⟨[78647], [78647], .contexts []⟩,
    ⟨[78645], [78645], .contexts []⟩,
    ⟨[78643], [78643], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [78643], .contexts [
        ⟨8836, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨8706, false, false, [], [15, 13, 1, 11]⟩,
        ⟨8837, false, false, [], [15, 13, 1, 11]⟩,
        ⟨8705, false, false, [], [15, 13, 1, 11]⟩,
        ⟨8705, false, false, [], [15, 13, 1, 11]⟩,
        ⟨8703, false, false, [], [13, 1, 11]⟩,
        ⟨8838, false, false, [], [13, 1, 11]⟩,
        ⟨8702, false, false, [], [13, 1, 11]⟩,
        ⟨8702, false, false, [], [13, 1, 11]⟩,
        ⟨8700, false, false, [], [1, 11]⟩,
        ⟨8839, false, false, [], [1, 11]⟩,
        ⟨8699, false, false, [], [1, 11]⟩,
        ⟨8699, false, false, [], [1, 11]⟩,
        ⟨8697, false, false, [], [11]⟩,
        ⟨8840, false, false, [], [11]⟩,
        ⟨8696, false, false, [], [11]⟩,
        ⟨8696, false, false, [], [11]⟩,
        ⟨8694, false, false, [], []⟩,
        ⟨8841, false, false, [], []⟩,
        ⟨8693, false, false, [], []⟩,
        ⟨8693, false, false, [], []⟩
      ]⟩,
    ⟨[78641], [78641], .contexts []⟩,
    ⟨[78639], [78639], .contexts []⟩,
    ⟨[78637], [78637], .contexts []⟩,
    ⟨[78637, 3], [78635], .contexts [
        ⟨8681, false, false, [], []⟩
      ]⟩,
    ⟨[78635], [78635], .contexts []⟩,
    ⟨[78635, 1], [78633], .contexts [
        ⟨8677, false, false, [], []⟩
      ]⟩,
    ⟨[78633], [78633], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [78633], .contexts [
        ⟨8842, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨8691, false, false, [], [1, 5, 3, 1]⟩,
        ⟨8843, false, false, [], [1, 5, 3, 1]⟩,
        ⟨8690, false, false, [], [1, 5, 3, 1]⟩,
        ⟨8690, false, false, [], [1, 5, 3, 1]⟩,
        ⟨8688, false, false, [], [5, 3, 1]⟩,
        ⟨8844, false, false, [], [5, 3, 1]⟩,
        ⟨8687, false, false, [], [5, 3, 1]⟩,
        ⟨8687, false, false, [], [5, 3, 1]⟩,
        ⟨8685, false, false, [], [3, 1]⟩,
        ⟨8845, false, false, [], [3, 1]⟩,
        ⟨8684, false, false, [], [3, 1]⟩,
        ⟨8684, false, false, [], [3, 1]⟩,
        ⟨8846, false, false, [], [1]⟩,
        ⟨8847, false, false, [], [1]⟩,
        ⟨8680, false, false, [], [1]⟩,
        ⟨8680, false, false, [], [1]⟩,
        ⟨8848, false, false, [], []⟩,
        ⟨8849, false, false, [], []⟩,
        ⟨8676, false, false, [], []⟩,
        ⟨8676, false, false, [], []⟩
      ]⟩,
    ⟨[78633, 15], [78631], .contexts [
        ⟨8673, false, false, [], []⟩
      ]⟩,
    ⟨[78631], [78631], .contexts []⟩,
    ⟨[78631, 13], [78629], .contexts [
        ⟨8669, false, false, [], []⟩
      ]⟩,
    ⟨[78629], [78629], .contexts []⟩,
    ⟨[78629, 1], [78627], .contexts [
        ⟨8665, false, false, [], []⟩
      ]⟩,
    ⟨[78627], [78627], .contexts []⟩,
    ⟨[78627, 11], [78625], .contexts [
        ⟨8661, false, false, [], []⟩
      ]⟩,
    ⟨[78625], [78625], .contexts []⟩,
    ⟨[78625, 9], [78623], .contexts [
        ⟨8657, false, false, [], []⟩
      ]⟩,
    ⟨[78623], [78623], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [78623], .contexts [
        ⟨8850, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨8851, false, false, [], [13, 1, 11, 9]⟩,
        ⟨8852, false, false, [], [13, 1, 11, 9]⟩,
        ⟨8672, false, false, [], [13, 1, 11, 9]⟩,
        ⟨8672, false, false, [], [13, 1, 11, 9]⟩,
        ⟨8853, false, false, [], [1, 11, 9]⟩,
        ⟨8854, false, false, [], [1, 11, 9]⟩,
        ⟨8668, false, false, [], [1, 11, 9]⟩,
        ⟨8668, false, false, [], [1, 11, 9]⟩,
        ⟨8855, false, false, [], [11, 9]⟩,
        ⟨8856, false, false, [], [11, 9]⟩,
        ⟨8664, false, false, [], [11, 9]⟩,
        ⟨8664, false, false, [], [11, 9]⟩,
        ⟨8857, false, false, [], [9]⟩,
        ⟨8858, false, false, [], [9]⟩,
        ⟨8660, false, false, [], [9]⟩,
        ⟨8660, false, false, [], [9]⟩,
        ⟨8859, false, false, [], []⟩,
        ⟨8860, false, false, [], []⟩,
        ⟨8656, false, false, [], []⟩,
        ⟨8656, false, false, [], []⟩
      ]⟩,
    ⟨[78623, 1], [78621], .contexts [
        ⟨8653, false, false, [], []⟩
      ]⟩,
    ⟨[78621], [78621], .contexts []⟩,
    ⟨[78619], [78619], .contexts []⟩,
    ⟨[78617], [78617], .contexts []⟩,
    ⟨[78615], [78615], .contexts []⟩,
    ⟨[78613], [78613], .contexts []⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [78613], .contexts [
        ⟨8861, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨8862, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8863, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8652, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8652, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8650, false, false, [], [3, 1, 15]⟩,
        ⟨8864, false, false, [], [3, 1, 15]⟩,
        ⟨8649, false, false, [], [3, 1, 15]⟩,
        ⟨8649, false, false, [], [3, 1, 15]⟩,
        ⟨8647, false, false, [], [1, 15]⟩,
        ⟨8865, false, false, [], [1, 15]⟩,
        ⟨8646, false, false, [], [1, 15]⟩,
        ⟨8646, false, false, [], [1, 15]⟩,
        ⟨8644, false, false, [], [15]⟩,
        ⟨8866, false, false, [], [15]⟩,
        ⟨8643, false, false, [], [15]⟩,
        ⟨8643, false, false, [], [15]⟩,
        ⟨8640, false, false, [], []⟩,
        ⟨8867, false, false, [], []⟩,
        ⟨8639, false, false, [], []⟩,
        ⟨8639, false, false, [], []⟩
      ]⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1
    ], [78603], .contexts [
        ⟨8868, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨8636, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8635, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8635, false, false, [], [1, 11, 9, 1]⟩,
        ⟨8631, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [78609], [11, 9, 1]⟩,
        ⟨8632, false, false, [], [11, 9, 1]⟩,
        ⟨8632, false, false, [], [11, 9, 1]⟩,
        ⟨8632, false, false, [], [11, 9, 1]⟩,
        ⟨8629, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [78607], [9, 1]⟩,
        ⟨8630, false, false, [], [9, 1]⟩,
        ⟨8630, false, false, [], [9, 1]⟩,
        ⟨8630, false, false, [], [9, 1]⟩,
        ⟨8627, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [78605], [1]⟩,
        ⟨8628, false, false, [], [1]⟩,
        ⟨8628, false, false, [], [1]⟩,
        ⟨8628, false, false, [], [1]⟩,
        ⟨8625, false, false, [], [1]⟩,
        ⟨18, false, false, [78603], []⟩,
        ⟨8626, false, false, [], []⟩,
        ⟨8626, false, false, [], []⟩,
        ⟨8626, false, false, [], []⟩
      ]⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [78595], .contexts [
        ⟨8869, false, false, [], [5, 3, 1, 15]⟩,
        ⟨8623, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [78601], [3, 1, 15]⟩,
        ⟨8624, false, false, [], [3, 1, 15]⟩,
        ⟨8624, false, false, [], [3, 1, 15]⟩,
        ⟨8624, false, false, [], [3, 1, 15]⟩,
        ⟨8621, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [78599], [1, 15]⟩,
        ⟨8622, false, false, [], [1, 15]⟩,
        ⟨8622, false, false, [], [1, 15]⟩,
        ⟨8622, false, false, [], [1, 15]⟩,
        ⟨8619, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [78597], [15]⟩,
        ⟨8620, false, false, [], [15]⟩,
        ⟨8620, false, false, [], [15]⟩,
        ⟨8620, false, false, [], [15]⟩,
        ⟨8617, false, false, [], [15]⟩,
        ⟨3, false, false, [78595], []⟩,
        ⟨8618, false, false, [], []⟩,
        ⟨8618, false, false, [], []⟩,
        ⟨8618, false, false, [], []⟩
      ]⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9
    ], [78587], .contexts [
        ⟨8870, false, false, [], [13, 1, 11, 9]⟩,
        ⟨8615, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [78593], [1, 11, 9]⟩,
        ⟨8616, false, false, [], [1, 11, 9]⟩,
        ⟨8616, false, false, [], [1, 11, 9]⟩,
        ⟨8616, false, false, [], [1, 11, 9]⟩,
        ⟨8613, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78591], [11, 9]⟩,
        ⟨8614, false, false, [], [11, 9]⟩,
        ⟨8614, false, false, [], [11, 9]⟩,
        ⟨8614, false, false, [], [11, 9]⟩,
        ⟨8611, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [78589], [9]⟩,
        ⟨8612, false, false, [], [9]⟩,
        ⟨8612, false, false, [], [9]⟩,
        ⟨8612, false, false, [], [9]⟩,
        ⟨8609, false, false, [], [9]⟩,
        ⟨76, false, false, [78587], []⟩,
        ⟨8610, false, false, [], []⟩,
        ⟨8610, false, false, [], []⟩,
        ⟨8610, false, false, [], []⟩
      ]⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [78579], .contexts [
        ⟨8871, false, false, [], [1, 5, 3, 1]⟩,
        ⟨8607, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78585], [5, 3, 1]⟩,
        ⟨8608, false, false, [], [5, 3, 1]⟩,
        ⟨8608, false, false, [], [5, 3, 1]⟩,
        ⟨8608, false, false, [], [5, 3, 1]⟩,
        ⟨8605, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78583], [3, 1]⟩,
        ⟨8606, false, false, [], [3, 1]⟩,
        ⟨8606, false, false, [], [3, 1]⟩,
        ⟨8606, false, false, [], [3, 1]⟩,
        ⟨8603, false, false, [], [3, 1]⟩,
        ⟨35, false, false, [78581], [1]⟩,
        ⟨8604, false, false, [], [1]⟩,
        ⟨8604, false, false, [], [1]⟩,
        ⟨8604, false, false, [], [1]⟩,
        ⟨8601, false, false, [], [1]⟩,
        ⟨18, false, false, [78579], []⟩,
        ⟨8602, false, false, [], []⟩,
        ⟨8602, false, false, [], []⟩,
        ⟨8602, false, false, [], []⟩
      ]⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [2003, 78573], .contexts [
        ⟨8872, false, false, [], [15, 13, 1, 11]⟩,
        ⟨8599, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [78577], [13, 1, 11]⟩,
        ⟨8600, false, false, [], [13, 1, 11]⟩,
        ⟨8600, false, false, [], [13, 1, 11]⟩,
        ⟨8600, false, false, [], [13, 1, 11]⟩,
        ⟨8598, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78575], [1, 11]⟩,
        ⟨8594, false, false, [], [1, 11]⟩,
        ⟨8593, false, false, [], [1, 11]⟩,
        ⟨8594, false, false, [], [1, 11]⟩,
        ⟨8594, false, false, [], [1, 11]⟩,
        ⟨8594, true, false, [], [1, 11]⟩,
        ⟨8594, true, false, [], [1, 11]⟩,
        ⟨8593, true, false, [], [1, 11]⟩,
        ⟨8592, true, false, [], [1, 11]⟩,
        ⟨992, false, false, [78573], [11]⟩,
        ⟨993, false, false, [78573], [11]⟩,
        ⟨8597, false, false, [], [11]⟩,
        ⟨8514, true, false, [], [78575, 11]⟩,
        ⟨8595, false, false, [], [11]⟩,
        ⟨8596, false, false, [], [11]⟩,
        ⟨8596, false, false, [], [11]⟩,
        ⟨8592, true, false, [2003], [11]⟩,
        ⟨90, false, false, [2003, 78573], []⟩,
        ⟨8582, false, false, [2003], []⟩,
        ⟨8587, false, false, [], []⟩,
        ⟨8588, false, false, [], []⟩,
        ⟨8589, false, false, [], []⟩
      ]⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [2003, 78565], .contexts [
        ⟨8873, false, false, [], [9, 1, 5, 3]⟩,
        ⟨8581, true, false, [2003], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [2003, 78571], [1, 5, 3]⟩,
        ⟨8583, false, false, [], [1, 5, 3]⟩,
        ⟨8584, false, false, [], [1, 5, 3]⟩,
        ⟨8585, false, false, [], [1, 5, 3]⟩,
        ⟨8579, false, false, [2003], [5, 3]⟩,
        ⟨8574, false, false, [], [5, 3]⟩,
        ⟨8575, false, false, [], [5, 3]⟩,
        ⟨8576, false, false, [], [5, 3]⟩,
        ⟨8570, true, false, [2003], [5, 3]⟩,
        ⟨49, false, false, [2003, 78567], [3]⟩,
        ⟨8564, false, false, [2003], [3]⟩,
        ⟨8565, false, false, [], [3]⟩,
        ⟨8566, false, false, [], [3]⟩,
        ⟨8567, false, false, [], [3]⟩,
        ⟨8563, true, false, [2003], [3]⟩,
        ⟨35, false, false, [2003, 78565], []⟩,
        ⟨8520, false, false, [2003], []⟩,
        ⟨8527, false, false, [], []⟩,
        ⟨8528, false, false, [], []⟩,
        ⟨8529, false, false, [], []⟩
      ]⟩,
    ⟨[2023], [2003, 1997], .source 1076⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [2023, 78557], .contexts [
        ⟨8874, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨8526, false, false, [2003], [15, 13, 1, 11]⟩,
        ⟨8875, true, false, [], [78565, 15, 13, 1, 11]⟩,
        ⟨8519, false, false, [2023], [13, 1, 11]⟩,
        ⟨8502, false, false, [2023], [1, 11]⟩,
        ⟨8463, false, false, [2023], [11]⟩,
        ⟨8447, false, false, [2023], []⟩
      ]⟩,
    ⟨[2025], [2023, 1905], .source 1077⟩,
    ⟨[2027], [2025, 1421], .source 1078⟩,
    ⟨[
      78713, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [2027, 77131], .contexts [
        ⟨8876, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨8424, false, false, [2023], [1, 5, 3, 1]⟩,
        ⟨8394, false, false, [2023], [5, 3, 1]⟩,
        ⟨8380, false, false, [2023], [3, 1]⟩,
        ⟨8102, false, false, [2023], [1]⟩,
        ⟨8877, true, false, [], [78257, 1]⟩,
        ⟨6643, false, false, [2025], []⟩,
        ⟨8878, true, false, [], [77131]⟩
      ]⟩,
    ⟨[2029], [2027, 539], .source 1079⟩,
    ⟨[2031], [2029, 269], .source 1080⟩,
    ⟨[78715, 11], [78715, 11], .contexts []⟩,
    ⟨[2031, 77869], [2031, 77869], .contexts []⟩,
    ⟨[78715, 11], [2031, 77869], .contexts [
        ⟨8882, false, false, [], []⟩,
        ⟨8882, false, false, [], []⟩,
        ⟨8800, true, false, [], [11]⟩,
        ⟨8800, true, false, [], [11]⟩,
        ⟨8798, true, false, [], [11]⟩,
        ⟨6139, false, false, [78713], []⟩,
        ⟨6147, false, false, [78713], []⟩,
        ⟨8879, false, false, [], [15, 13, 1]⟩,
        ⟨445, false, false, [2027], [13, 1]⟩,
        ⟨4930, false, false, [2027], [1]⟩,
        ⟨8880, true, false, [], [77869, 1]⟩,
        ⟨4920, false, false, [2029], []⟩,
        ⟨8881, true, false, [], [77869]⟩,
        ⟨4919, false, false, [2031], []⟩,
        ⟨24, true, false, [], [2031, 77869]⟩,
        ⟨8883, false, false, [], []⟩
      ]⟩,
    ⟨[78715, 11], [2031, 77869], .contexts [
        ⟨8884, false, false, [], []⟩,
        ⟨8883, false, false, [], []⟩
      ]⟩,
    ⟨[78715], [78715], .contexts []⟩,
    ⟨[78715], [78715], .contexts []⟩,
    ⟨[2051], [2031, 537], .source 1090⟩,
    ⟨[2053], [2051, 1855], .source 1091⟩,
    ⟨[78537, 13], [78537, 13], .contexts []⟩,
    ⟨[2055], [2052], .source 1092⟩,
    ⟨[2052], [2052], .contexts []⟩,
    ⟨[78537, 13], [2055, 78715], .contexts [
        ⟨8890, false, false, [], []⟩,
        ⟨8889, false, false, [2052], [78537, 13]⟩,
        ⟨8005, true, false, [2052, 2051], [13]⟩,
        ⟨8888, false, false, [2052], [77133, 11, 13]⟩,
        ⟨4929, true, false, [2052, 2031], [11, 13]⟩,
        ⟨8885, true, false, [2052], [13, 11, 13]⟩,
        ⟨1836, false, false, [2052, 78715], []⟩,
        ⟨8886, false, false, [2052], []⟩,
        ⟨8887, false, false, [2052], []⟩,
        ⟨8892, true, false, [], [78715]⟩,
        ⟨8892, true, false, [], [78715]⟩,
        ⟨8891, true, false, [], [78715]⟩
      ]⟩,
    ⟨[2053], [2054], .contexts [
        ⟨8891, true, true, [], []⟩
      ]⟩,
    ⟨[78715, 13], [2053, 78537], .contexts [
        ⟨8893, true, false, [2054], [13]⟩,
        ⟨98, false, false, [2054, 78537], []⟩,
        ⟨8894, true, false, [], [78537]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 139. -/
def y322TCContextRaw139 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2057], [2031, 1067], .source 1093⟩,
    ⟨[11, 15, 11, 15], [], .contexts [
        ⟨357, false, false, [], []⟩
      ]⟩,
    ⟨[2059], [2056], .source 1094⟩,
    ⟨[2056], [2056], .contexts []⟩,
    ⟨[77455, 15], [2059, 78715], .contexts [
        ⟨8896, false, false, [2056], [77455, 15]⟩,
        ⟨4908, true, false, [2056, 2031], [15]⟩,
        ⟨4913, true, false, [2056, 2031], [11, 15]⟩,
        ⟨8885, true, false, [2056], [15, 11, 15]⟩,
        ⟨8897, false, false, [2056, 78715], []⟩,
        ⟨8886, false, false, [2056], []⟩,
        ⟨8887, false, false, [2056], []⟩,
        ⟨8899, true, false, [], [78715]⟩,
        ⟨8899, true, false, [], [78715]⟩,
        ⟨8898, true, false, [], [78715]⟩
      ]⟩,
    ⟨[2055, 78715], [2055, 78715], .contexts []⟩,
    ⟨[2063], [2053, 1825], .source 1096⟩,
    ⟨[2065], [2062], .source 1097⟩,
    ⟨[765, 77609], [765, 77609], .contexts []⟩,
    ⟨[765, 77609], [2065, 78713], .contexts [
        ⟨8904, true, false, [], []⟩,
        ⟨8904, true, false, [], []⟩,
        ⟨3653, true, false, [], []⟩,
        ⟨3650, true, false, [], []⟩,
        ⟨8902, false, false, [2062], [77495, 13]⟩,
        ⟨8894, false, false, [2062], [1825, 77495, 13]⟩,
        ⟨2961, true, false, [2062, 2054, 1825], [13]⟩,
        ⟨7963, true, false, [2062, 2054], [13]⟩,
        ⟨77, true, false, [2062, 2054, 78537], [13]⟩,
        ⟨1650, true, false, [2062, 2054, 78537], [13]⟩,
        ⟨8890, false, false, [2062, 2054], [9, 13, 13]⟩,
        ⟨8893, false, false, [2062, 2054], [9, 13, 13]⟩,
        ⟨8901, false, false, [2062, 2054], [9, 13, 13]⟩,
        ⟨8901, false, false, [2062, 2054], [9, 13, 13]⟩,
        ⟨8799, false, false, [2062], [13, 13]⟩,
        ⟨98, false, false, [2062, 78713], []⟩,
        ⟨8903, true, false, [], [78713]⟩
      ]⟩,
    ⟨[2067], [763, 2065], .source 1098⟩,
    ⟨[2069], [2066], .source 1099⟩,
    ⟨[78713], [2069, 77609], .contexts [
        ⟨8906, false, false, [2066], [78713]⟩,
        ⟨3654, false, false, [2066], [2065, 78713]⟩,
        ⟨8905, true, false, [2066, 764], []⟩,
        ⟨8907, true, false, [], [77609]⟩
      ]⟩,
    ⟨[2069, 77607], [2069, 77607], .contexts []⟩,
    ⟨[2071], [2069, 463], .source 1100⟩,
    ⟨[2073], [2070], .source 1101⟩,
    ⟨[77607], [2073, 78709], .contexts [
        ⟨8910, false, false, [2070], [77607]⟩,
        ⟨3623, true, false, [2070, 2069], []⟩,
        ⟨8909, true, false, [2070], [5]⟩,
        ⟨8907, false, false, [2070], [77607, 5]⟩,
        ⟨8909, true, false, [2070, 2066, 2068], [5]⟩,
        ⟨3631, true, false, [2070, 2066], [5]⟩,
        ⟨8908, true, false, [2070, 2066, 2068], [1, 5]⟩,
        ⟨8796, false, false, [2070, 2066, 2068], [5]⟩,
        ⟨8801, false, false, [2070, 2066, 2068], [5]⟩,
        ⟨24, true, false, [2070, 2066, 2068], [78711, 5]⟩,
        ⟨8907, false, true, [2070, 2066], [78711, 5]⟩,
        ⟨8793, false, false, [2070], []⟩,
        ⟨8802, false, false, [2070], []⟩,
        ⟨24, true, false, [2070], [78709]⟩,
        ⟨8911, true, false, [], [78709]⟩
      ]⟩,
    ⟨[2075], [2071, 433], .source 1102⟩,
    ⟨[2077], [2074], .source 1103⟩,
    ⟨[2077], [2074], .contexts [
        ⟨8914, false, false, [], []⟩,
        ⟨24, false, false, [2074], []⟩
      ]⟩,
    ⟨[2075], [2076], .contexts [
        ⟨8914, true, true, [], []⟩
      ]⟩,
    ⟨[78707, 1], [2075, 77609], .contexts [
        ⟨8915, false, false, [2076], [78707, 1]⟩,
        ⟨8803, true, false, [2076, 2074], [1]⟩,
        ⟨8790, true, false, [2076, 2074], [1]⟩,
        ⟨8912, true, false, [2076, 2074, 2072], [3, 1]⟩,
        ⟨8911, false, true, [2076, 2074], [77607, 3, 1]⟩,
        ⟨3618, false, false, [2076, 2074, 2071], [1]⟩,
        ⟨8913, true, false, [2076, 2074], [77607, 1]⟩,
        ⟨8916, true, false, [], [77607, 1]⟩,
        ⟨3630, false, false, [2075], []⟩
      ]⟩,
    ⟨[2075, 77609], [2075, 77609], .contexts []⟩,
    ⟨[2079], [2075, 461], .source 1104⟩,
    ⟨[2081], [2078], .source 1105⟩,
    ⟨[78703], [2079, 77461], .contexts [
        ⟨8920, false, false, [2080], [78703]⟩,
        ⟨24, false, false, [2080, 2078], [78703]⟩,
        ⟨8805, true, false, [2080, 2078], []⟩,
        ⟨8784, true, false, [2080, 2078], []⟩,
        ⟨8915, false, false, [2080, 2078, 2076], [78705, 15]⟩,
        ⟨8804, true, false, [2080, 2078, 2076, 2074], [15]⟩,
        ⟨8787, true, false, [2080, 2078, 2076, 2074], [15]⟩,
        ⟨8917, false, false, [2080, 2078, 2076, 2074], [15]⟩,
        ⟨8918, false, false, [2080, 2078, 2076, 2074], [15]⟩,
        ⟨8916, true, false, [2080, 2078], [77609, 15]⟩,
        ⟨8918, false, false, [2080, 2078], [15]⟩,
        ⟨3643, false, false, [2080, 2078, 2075], []⟩,
        ⟨8919, true, false, [2080, 2078], [77461]⟩,
        ⟨8920, false, true, [], [77461]⟩
      ]⟩,
    ⟨[2083], [2079, 685], .source 1106⟩,
    ⟨[2085], [2082], .source 1107⟩,
    ⟨[2085], [2082], .contexts [
        ⟨8923, false, false, [], []⟩,
        ⟨24, false, false, [2082], []⟩
      ]⟩,
    ⟨[2083], [2084], .contexts [
        ⟨8923, true, true, [], []⟩
      ]⟩,
    ⟨[2083, 77603], [2083, 77603], .contexts []⟩,
    ⟨[2083, 77603], [78699], .contexts [
        ⟨8926, true, false, [], []⟩,
        ⟨3149, true, false, [2083], []⟩,
        ⟨8925, false, false, [], [77601, 1]⟩,
        ⟨8922, false, false, [2084, 2082], [77601, 1]⟩,
        ⟨3343, true, false, [2084, 2082, 2079], [1]⟩,
        ⟨8921, true, false, [2084, 2082], [13, 1]⟩,
        ⟨8781, false, false, [2084, 2082], [1]⟩,
        ⟨8807, false, false, [2084, 2082], [1]⟩,
        ⟨8924, true, false, [2084], [78701, 1]⟩,
        ⟨8778, false, false, [], []⟩,
        ⟨8808, false, false, [], []⟩
      ]⟩,
    ⟨[2087], [2083, 651], .source 1108⟩,
    ⟨[2089], [2086], .source 1109⟩,
    ⟨[78697, 9], [2087, 643, 77487], .contexts [
        ⟨8929, false, false, [2088], [78697, 9]⟩,
        ⟨24, false, false, [2088, 2086], [78697, 9]⟩,
        ⟨8809, true, false, [2088, 2086], [9]⟩,
        ⟨8775, true, false, [2088, 2086], [9]⟩,
        ⟨8924, false, false, [2088, 2086, 2084], [78699, 11, 9]⟩,
        ⟨8927, true, false, [2088, 2086, 2084, 2082], [11, 9]⟩,
        ⟨8925, true, false, [2088, 2086], [77603, 11, 9]⟩,
        ⟨8926, false, false, [2088, 2086], [11, 9]⟩,
        ⟨3288, false, false, [2088, 2086, 2083], [9]⟩,
        ⟨8928, true, false, [2088, 2086], [77603, 9]⟩,
        ⟨8929, false, true, [], [77603, 9]⟩,
        ⟨3282, false, false, [2087], []⟩
      ]⟩,
    ⟨[2091], [2087, 643], .source 1110⟩,
    ⟨[2093], [2090], .source 1111⟩,
    ⟨[2093], [2090], .contexts [
        ⟨8932, false, false, [], []⟩,
        ⟨24, false, false, [2090], []⟩
      ]⟩,
    ⟨[2091], [2092], .contexts [
        ⟨8932, true, true, [], []⟩
      ]⟩,
    ⟨[2091, 77343], [2091, 77343], .contexts []⟩,
    ⟨[78693], [2091, 77343], .contexts [
        ⟨8933, false, false, [2092], [78693]⟩,
        ⟨8811, true, false, [2092, 2090], []⟩,
        ⟨8769, true, false, [2092, 2090], []⟩,
        ⟨8933, false, false, [2092, 2090, 2092], [78695, 1]⟩,
        ⟨8810, true, false, [2092, 2090, 2092, 2090], [1]⟩,
        ⟨8772, true, false, [2092, 2090, 2092, 2090], [1]⟩,
        ⟨8930, false, false, [2092, 2090, 2092, 2090], [1]⟩,
        ⟨8931, true, false, [2092, 2090, 2092, 2090], [77487, 1]⟩,
        ⟨8934, true, false, [2092, 2090], [77487, 1]⟩,
        ⟨2775, false, false, [2092], []⟩,
        ⟨8935, false, false, [2092, 2090], []⟩,
        ⟨8934, true, false, [], [77343]⟩
      ]⟩,
    ⟨[2095], [2091, 267], .source 1112⟩,
    ⟨[2097], [2094], .source 1113⟩,
    ⟨[2099], [2095, 493], .source 1114⟩,
    ⟨[2099, 77343], [78689], .contexts [
        ⟨8939, false, false, [], [77343]⟩,
        ⟨2619, true, false, [2095], []⟩,
        ⟨8938, true, true, [], [77343, 3]⟩,
        ⟨8937, false, false, [2096, 2094], [77343, 3]⟩,
        ⟨1647, true, false, [2096, 2094, 2091], [3]⟩,
        ⟨8935, true, false, [2096, 2094], [5, 3]⟩,
        ⟨8936, true, false, [2096, 2094], [5, 3]⟩,
        ⟨8766, false, false, [2096, 2094], [3]⟩,
        ⟨8813, false, false, [2096, 2094], [3]⟩,
        ⟨24, true, false, [2096, 2094], [78691, 3]⟩,
        ⟨8938, true, false, [2096], [78691, 3]⟩,
        ⟨8763, false, false, [], []⟩
      ]⟩,
    ⟨[2101], [2098], .source 1115⟩,
    ⟨[2101], [2098], .contexts [
        ⟨8941, false, false, [], []⟩,
        ⟨24, false, false, [2098], []⟩
      ]⟩,
    ⟨[2099], [2100], .contexts [
        ⟨8941, true, true, [], []⟩
      ]⟩,
    ⟨[2099, 77487], [2099, 77487], .contexts []⟩,
    ⟨[78687, 15], [2099, 503, 77119], .contexts [
        ⟨8942, false, false, [2100], [78687, 15]⟩,
        ⟨8815, true, false, [2100, 2098], [15]⟩,
        ⟨8760, true, false, [2100, 2098], [15]⟩,
        ⟨8942, false, false, [2100, 2098, 2100], [78689, 1, 15]⟩,
        ⟨8814, true, false, [2100, 2098, 2100, 2098], [1, 15]⟩,
        ⟨8940, true, false, [2100, 2098, 2100, 2098], [1, 15]⟩,
        ⟨8943, true, false, [2100, 2098], [77343, 1, 15]⟩,
        ⟨2774, false, false, [2100], [15]⟩,
        ⟨8944, false, false, [2100, 2098], [15]⟩,
        ⟨8943, true, false, [], [77487, 15]⟩,
        ⟨8944, false, false, [], [15]⟩,
        ⟨2772, true, false, [2099, 504], [15]⟩,
        ⟨3, false, false, [2099, 504, 77119], []⟩,
        ⟨2773, true, false, [2099], [77119]⟩
      ]⟩,
    ⟨[2103], [2099, 503], .source 1116⟩,
    ⟨[2105], [2102], .source 1117⟩,
    ⟨[2107], [2103, 31], .source 1118⟩,
    ⟨[2109], [2106], .source 1119⟩,
    ⟨[78683], [2108, 77119], .contexts [
        ⟨8949, false, false, [2108], [78683]⟩,
        ⟨24, false, false, [2108, 2106], [78683]⟩,
        ⟨8817, true, false, [2108, 2106], []⟩,
        ⟨8754, true, false, [2108, 2106], []⟩,
        ⟨8947, false, false, [2108, 2106, 2104], [78685, 13]⟩,
        ⟨24, false, false, [2108, 2106, 2104, 2102], [78685, 13]⟩,
        ⟨8816, true, false, [2108, 2106, 2104, 2102], [13]⟩,
        ⟨8757, true, false, [2108, 2106, 2104, 2102], [13]⟩,
        ⟨8945, false, false, [2108, 2106, 2104, 2102], [13]⟩,
        ⟨8946, true, false, [2108, 2106, 2104, 2102], [77119, 13]⟩,
        ⟨8947, false, true, [2108, 2106], [77119, 13]⟩,
        ⟨422, false, false, [2108, 2106, 2103], []⟩,
        ⟨740, true, false, [2108, 2106, 2103], [77119]⟩,
        ⟨8948, true, false, [2108, 2106], [77119]⟩
      ]⟩,
    ⟨[2111], [2107, 317], .source 1120⟩,
    ⟨[2113], [2110], .source 1121⟩,
    ⟨[78681, 11], [2111, 847, 77711], .contexts [
        ⟨8952, false, false, [2112], [78681, 11]⟩,
        ⟨24, false, false, [2112, 2110], [78681, 11]⟩,
        ⟨8819, true, false, [2112, 2110], [11]⟩,
        ⟨8751, true, false, [2112, 2110], [11]⟩,
        ⟨8950, false, false, [2112, 2110], [1, 11]⟩,
        ⟨8949, false, true, [2112, 2110], [77119, 1, 11]⟩,
        ⟨1945, false, false, [2112, 2110, 2107], [11]⟩,
        ⟨8951, true, false, [2112, 2110], [77123, 11]⟩,
        ⟨8952, false, true, [], [77123, 11]⟩,
        ⟨4054, false, false, [2111], []⟩
      ]⟩,
    ⟨[2115], [2111, 847], .source 1122⟩,
    ⟨[2117], [2114], .source 1123⟩,
    ⟨[2119], [2115, 1189], .source 1124⟩,
    ⟨[2121], [2118], .source 1125⟩,
    ⟨[78677], [2119, 77971], .contexts [
        ⟨8957, false, false, [2120], [78677]⟩,
        ⟨24, false, false, [2120, 2118], [78677]⟩,
        ⟨8821, true, false, [2120, 2118], []⟩,
        ⟨8745, true, false, [2120, 2118], []⟩,
        ⟨8955, false, false, [2120, 2118, 2116], [78679, 9]⟩,
        ⟨24, false, false, [2120, 2118, 2116, 2114], [78679, 9]⟩,
        ⟨8820, true, false, [2120, 2118, 2116, 2114], [9]⟩,
        ⟨8748, true, false, [2120, 2118, 2116, 2114], [9]⟩,
        ⟨8953, false, false, [2120, 2118, 2116, 2114], [9]⟩,
        ⟨8954, true, false, [2120, 2118, 2116, 2114], [77711, 9]⟩,
        ⟨8955, false, true, [2120, 2118], [77711, 9]⟩,
        ⟨5345, false, false, [2120, 2118, 2115], []⟩,
        ⟨8956, true, false, [2120, 2118], [77971]⟩,
        ⟨8957, false, true, [], [77971]⟩
      ]⟩,
    ⟨[2123], [2119, 1161], .source 1126⟩]

/-- Exact literal claimed equations and contextual derivations, block 140. -/
def y322TCContextRaw140 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2125], [2122], .source 1127⟩,
    ⟨[2127], [2123, 1191], .source 1128⟩,
    ⟨[2127, 77971], [78673], .contexts [
        ⟨8961, false, false, [], [77971]⟩,
        ⟨5353, true, false, [2123], []⟩,
        ⟨8960, true, true, [], [77971, 5]⟩,
        ⟨8959, false, false, [2124, 2122], [77971, 5]⟩,
        ⟨5357, true, false, [2124, 2122, 2119], [5]⟩,
        ⟨8958, true, false, [2124, 2122], [1, 5]⟩,
        ⟨8742, false, false, [2124, 2122], [5]⟩,
        ⟨8822, false, false, [2124, 2122], [5]⟩,
        ⟨24, true, false, [2124, 2122], [78675, 5]⟩,
        ⟨8960, true, false, [2124], [78675, 5]⟩,
        ⟨8739, false, false, [], []⟩,
        ⟨8823, false, false, [], []⟩
      ]⟩,
    ⟨[2129], [2126], .source 1129⟩,
    ⟨[2131], [2127, 1193], .source 1130⟩,
    ⟨[2133], [2130], .source 1131⟩,
    ⟨[78671], [2131, 77971], .contexts [
        ⟨8965, false, false, [2132], [78671]⟩,
        ⟨24, false, false, [2132, 2130], [78671]⟩,
        ⟨8825, true, false, [2132, 2130], []⟩,
        ⟨8736, true, false, [2132, 2130], []⟩,
        ⟨8963, false, false, [2132, 2130, 2128], [78673, 3]⟩,
        ⟨24, false, false, [2132, 2130, 2128, 2126], [78673, 3]⟩,
        ⟨8962, true, false, [2132, 2130, 2128, 2126], [3]⟩,
        ⟨8963, false, true, [2132, 2130], [77971, 3]⟩,
        ⟨5359, false, false, [2132, 2130, 2127], []⟩,
        ⟨5342, false, false, [2132, 2130, 2127, 1166], []⟩,
        ⟨5361, true, false, [2132, 2130, 2127], [77971]⟩,
        ⟨5361, true, false, [2132, 2130, 2127], [77971]⟩,
        ⟨5360, true, false, [2132, 2130, 2127], [77971]⟩,
        ⟨8964, true, false, [2132, 2130], [77971]⟩,
        ⟨8965, false, true, [], [77971]⟩
      ]⟩,
    ⟨[2135], [2131, 1161], .source 1132⟩,
    ⟨[2137], [2134], .source 1133⟩,
    ⟨[2137], [2134], .contexts [
        ⟨8968, false, false, [], []⟩,
        ⟨24, false, false, [2134], []⟩
      ]⟩,
    ⟨[2135], [2136], .contexts [
        ⟨8968, true, true, [], []⟩
      ]⟩,
    ⟨[2135, 77973], [2135, 77973], .contexts []⟩,
    ⟨[2135, 77973], [78667], .contexts [
        ⟨8971, true, false, [], []⟩,
        ⟨5148, true, false, [2135], []⟩,
        ⟨8970, false, false, [], [77971, 15]⟩,
        ⟨8967, false, false, [2136, 2134], [77971, 15]⟩,
        ⟨5357, true, false, [2136, 2134, 2131], [15]⟩,
        ⟨8966, true, false, [2136, 2134], [1, 15]⟩,
        ⟨8733, false, false, [2136, 2134], [15]⟩,
        ⟨8826, false, false, [2136, 2134], [15]⟩,
        ⟨8969, true, false, [2136], [78669, 15]⟩,
        ⟨8730, false, false, [], []⟩,
        ⟨8827, false, false, [], []⟩
      ]⟩,
    ⟨[2139], [2135, 1185], .source 1134⟩,
    ⟨[2141], [2138], .source 1135⟩,
    ⟨[78665, 1], [2139, 1163, 77973], .contexts [
        ⟨8974, false, false, [2140], [78665, 1]⟩,
        ⟨24, false, false, [2140, 2138], [78665, 1]⟩,
        ⟨8828, true, false, [2140, 2138], [1]⟩,
        ⟨8727, true, false, [2140, 2138], [1]⟩,
        ⟨8969, false, false, [2140, 2138, 2136], [78667, 13, 1]⟩,
        ⟨8972, true, false, [2140, 2138, 2136, 2134], [13, 1]⟩,
        ⟨8970, true, false, [2140, 2138], [77973, 13, 1]⟩,
        ⟨8971, false, false, [2140, 2138], [13, 1]⟩,
        ⟨5337, false, false, [2140, 2138, 2135], [1]⟩,
        ⟨8973, true, false, [2140, 2138], [77973, 1]⟩,
        ⟨8974, false, true, [], [77973, 1]⟩,
        ⟨5152, false, false, [2139], []⟩,
        ⟨5320, false, false, [2139], []⟩
      ]⟩,
    ⟨[2143], [2139, 1163], .source 1136⟩,
    ⟨[2145], [2142], .source 1137⟩,
    ⟨[2147], [2143, 1317], .source 1138⟩,
    ⟨[2149], [2146], .source 1139⟩,
    ⟨[78275], [2149, 78661], .contexts [
        ⟨8978, false, false, [2146], [78275]⟩,
        ⟨5852, false, false, [2146, 2143], [78275]⟩,
        ⟨90, true, false, [2146, 2143, 1314, 78275], []⟩,
        ⟨6842, true, false, [2146, 2143, 1314], [11, 11]⟩,
        ⟨89, false, false, [2146, 2143, 1314, 78011], [11]⟩,
        ⟨92, false, false, [2146, 2143, 1314, 78011], [11]⟩,
        ⟨6822, false, false, [2146, 2143, 1314], [15, 11]⟩,
        ⟨5148, false, false, [2146, 2143], [11]⟩,
        ⟨5333, false, false, [2146, 2143], [11]⟩,
        ⟨5850, true, false, [2146, 2143, 1314], [77973, 11]⟩,
        ⟨8977, true, true, [2146], [77973, 11]⟩,
        ⟨8976, false, false, [2146, 2144, 2142], [77973, 11]⟩,
        ⟨8975, true, false, [2146, 2144, 2142], [11]⟩,
        ⟨8724, false, false, [2146, 2144, 2142], [11]⟩,
        ⟨8829, false, false, [2146, 2144, 2142], [11]⟩,
        ⟨24, true, false, [2146, 2144, 2142], [78663, 11]⟩,
        ⟨8977, true, false, [2146, 2144], [78663, 11]⟩,
        ⟨8721, false, false, [2146], []⟩,
        ⟨8831, false, false, [2146], []⟩,
        ⟨24, true, false, [2146], [78661]⟩,
        ⟨8979, true, false, [], [78661]⟩
      ]⟩,
    ⟨[2151], [2147, 539], .source 1140⟩,
    ⟨[2153], [2150], .source 1141⟩,
    ⟨[2153], [2150], .contexts [
        ⟨8982, false, false, [], []⟩,
        ⟨24, false, false, [2150], []⟩
      ]⟩,
    ⟨[2151], [2152], .contexts [
        ⟨8982, true, true, [], []⟩
      ]⟩,
    ⟨[78659], [2151, 77863], .contexts [
        ⟨8983, false, false, [2152], [78659]⟩,
        ⟨8832, true, false, [2152, 2150], []⟩,
        ⟨8718, true, false, [2152, 2150], []⟩,
        ⟨8980, true, false, [2152, 2150, 2148], [9]⟩,
        ⟨8979, false, true, [2152, 2150], [78275, 9]⟩,
        ⟨6842, true, false, [2152, 2150, 2147], [9]⟩,
        ⟨75, false, false, [2152, 2150, 2147, 78011], []⟩,
        ⟨78, false, false, [2152, 2150, 2147, 78011], []⟩,
        ⟨6820, false, false, [2152, 2150, 2147], [15]⟩,
        ⟨4844, false, false, [2152, 2150, 2147], []⟩,
        ⟨6266, false, false, [2152, 2150, 2147], []⟩,
        ⟨6266, false, false, [2152, 2150, 2147], []⟩,
        ⟨4828, false, false, [2152, 2150, 2147, 539], []⟩,
        ⟨5823, true, false, [2152, 2150, 2147], [77863]⟩,
        ⟨8981, true, false, [2152, 2150], [77863]⟩,
        ⟨8984, true, false, [], [77863]⟩
      ]⟩,
    ⟨[2151, 77865], [2151, 77865], .contexts []⟩,
    ⟨[2155], [2151, 261], .source 1142⟩,
    ⟨[2155, 77865], [78655], .contexts [
        ⟨8987, false, false, [], [77865]⟩,
        ⟨4855, true, false, [2151], []⟩,
        ⟨8986, true, false, [], [5]⟩,
        ⟨8984, false, false, [], [77865, 5]⟩,
        ⟨8986, true, false, [2152, 2150], [5]⟩,
        ⟨4846, true, false, [2152], [5]⟩,
        ⟨8985, true, false, [2152, 2150], [1, 5]⟩,
        ⟨8715, false, false, [2152, 2150], [5]⟩,
        ⟨8833, false, false, [2152, 2150], [5]⟩,
        ⟨8983, true, false, [2152], [78657, 5]⟩,
        ⟨8712, false, false, [], []⟩,
        ⟨8834, false, false, [], []⟩
      ]⟩,
    ⟨[2157], [2154], .source 1143⟩,
    ⟨[2159], [2155, 537], .source 1144⟩,
    ⟨[2161], [2158], .source 1145⟩,
    ⟨[78653], [2159, 78409], .contexts [
        ⟨8991, false, false, [2160], [78653]⟩,
        ⟨24, false, false, [2160, 2158], [78653]⟩,
        ⟨8835, true, false, [2160, 2158], []⟩,
        ⟨8709, true, false, [2160, 2158], []⟩,
        ⟨8989, false, false, [2160, 2158, 2156], [78655, 3]⟩,
        ⟨24, false, false, [2160, 2158, 2156, 2154], [78655, 3]⟩,
        ⟨8988, true, false, [2160, 2158, 2156, 2154], [3]⟩,
        ⟨8989, false, true, [2160, 2158], [77865, 3]⟩,
        ⟨7661, false, false, [2160, 2158, 2155], []⟩,
        ⟨8990, true, false, [2160, 2158], [78409]⟩,
        ⟨8991, false, true, [], [78409]⟩
      ]⟩,
    ⟨[2163], [2159, 323], .source 1146⟩,
    ⟨[2165], [2162], .source 1147⟩,
    ⟨[2165], [2162], .contexts [
        ⟨8994, false, false, [], []⟩,
        ⟨24, false, false, [2162], []⟩
      ]⟩,
    ⟨[2163], [2164], .contexts [
        ⟨8994, true, true, [], []⟩
      ]⟩,
    ⟨[78651], [2163, 78409], .contexts [
        ⟨8995, false, false, [2164], [78651]⟩,
        ⟨8837, true, false, [2164, 2162], []⟩,
        ⟨8706, true, false, [2164, 2162], []⟩,
        ⟨8992, false, false, [2164, 2162], [1]⟩,
        ⟨7655, true, false, [2164, 2162, 2159], [1]⟩,
        ⟨17, false, false, [2164, 2162, 2159, 78259], []⟩,
        ⟨21, false, false, [2164, 2162, 2159, 78259], []⟩,
        ⟨7526, false, false, [2164, 2162, 2159], [15]⟩,
        ⟨7652, false, false, [2164, 2162, 2159, 323], []⟩,
        ⟨5655, true, false, [2164, 2162, 2159], [78409]⟩,
        ⟨8993, true, false, [2164, 2162], [78409]⟩,
        ⟨8996, true, false, [], [78409]⟩
      ]⟩,
    ⟨[2163, 78259], [2163, 78259], .contexts []⟩,
    ⟨[2163, 78407], [2163, 78407], .contexts []⟩,
    ⟨[2163, 78407], [78647], .contexts [
        ⟨8999, true, false, [], []⟩,
        ⟨7533, true, false, [2163], []⟩,
        ⟨8998, true, false, [], [13]⟩,
        ⟨8996, false, false, [], [78259, 13]⟩,
        ⟨8998, true, false, [2164, 2162], [13]⟩,
        ⟨7653, true, false, [2164], [13]⟩,
        ⟨8997, true, false, [2164, 2162], [15, 13]⟩,
        ⟨8703, false, false, [2164, 2162], [13]⟩,
        ⟨8838, false, false, [2164, 2162], [13]⟩,
        ⟨8995, true, false, [2164], [78649, 13]⟩,
        ⟨8700, false, false, [], []⟩,
        ⟨8839, false, false, [], []⟩
      ]⟩,
    ⟨[2167], [2163, 1279], .source 1148⟩,
    ⟨[2169], [2166], .source 1149⟩,
    ⟨[2169], [2166], .contexts [
        ⟨9002, false, false, [], []⟩,
        ⟨24, false, false, [2166], []⟩
      ]⟩,
    ⟨[2167], [2168], .contexts [
        ⟨9002, true, true, [], []⟩
      ]⟩,
    ⟨[78645, 11], [2167, 77327], .contexts [
        ⟨9003, false, false, [2168], [78645, 11]⟩,
        ⟨8840, true, false, [2168, 2166], [11]⟩,
        ⟨8697, true, false, [2168, 2166], [11]⟩,
        ⟨8995, false, false, [2168, 2166, 2164], [78647, 1, 11]⟩,
        ⟨9000, true, false, [2168, 2166, 2164, 2162], [1, 11]⟩,
        ⟨8996, true, false, [2168, 2166], [78407, 1, 11]⟩,
        ⟨8999, false, false, [2168, 2166], [1, 11]⟩,
        ⟨7558, false, false, [2168, 2166, 2163], [11]⟩,
        ⟨9001, true, false, [2168, 2166], [77325, 11]⟩,
        ⟨9004, true, false, [], [77325, 11]⟩,
        ⟨1303, false, false, [2167], []⟩
      ]⟩,
    ⟨[2167, 77327], [2167, 77327], .contexts []⟩,
    ⟨[2171], [2167, 731], .source 1150⟩,
    ⟨[2173], [2170], .source 1151⟩,
    ⟨[2173], [2170], .contexts [
        ⟨9008, false, false, [], []⟩
      ]⟩,
    ⟨[2173], [2170], .contexts [
        ⟨9009, false, false, [], []⟩,
        ⟨24, false, false, [2170], []⟩
      ]⟩,
    ⟨[2171], [2172], .contexts [
        ⟨9008, true, true, [], []⟩
      ]⟩,
    ⟨[78641], [2171, 77193], .contexts [
        ⟨9010, false, false, [2172], [78641]⟩,
        ⟨8843, true, false, [2172, 2170], []⟩,
        ⟨8691, true, false, [2172, 2170], []⟩,
        ⟨9003, false, false, [2172, 2170, 2168], [78643, 9]⟩,
        ⟨8841, true, false, [2172, 2170, 2168, 2166], [9]⟩,
        ⟨8694, true, false, [2172, 2170, 2168, 2166], [9]⟩,
        ⟨9005, false, false, [2172, 2170, 2168, 2166], [9]⟩,
        ⟨9006, false, false, [2172, 2170, 2168, 2166], [9]⟩,
        ⟨9004, true, false, [2172, 2170], [77327, 9]⟩,
        ⟨9006, false, false, [2172, 2170], [9]⟩,
        ⟨3437, false, false, [2172, 2170, 2167], []⟩,
        ⟨9007, true, false, [2172, 2170], [77193]⟩,
        ⟨9011, true, false, [], [77193]⟩
      ]⟩,
    ⟨[2171, 77195], [2171, 77195], .contexts []⟩,
    ⟨[78639], [2171, 77195], .contexts [
        ⟨9010, false, false, [2172], [78639]⟩,
        ⟨8844, true, false, [2172, 2170], []⟩,
        ⟨8688, true, false, [2172, 2170], []⟩,
        ⟨9012, false, false, [2172, 2170], [1]⟩,
        ⟨553, false, false, [2172], []⟩,
        ⟨9013, false, false, [2172, 2170], []⟩,
        ⟨9011, true, false, [], [77195]⟩
      ]⟩,
    ⟨[2170], [2170], .contexts []⟩,
    ⟨[77195, 5], [2173, 78637], .contexts [
        ⟨9014, true, false, [2170], [5]⟩,
        ⟨8685, false, false, [2170], []⟩,
        ⟨8845, false, false, [2170], []⟩,
        ⟨9015, true, false, [], [78637]⟩,
        ⟨9015, true, false, [], [78637]⟩,
        ⟨9009, true, false, [], [78637]⟩
      ]⟩,
    ⟨[77195, 5], [2173, 78637], .contexts [
        ⟨9016, false, false, [], []⟩
      ]⟩,
    ⟨[2173, 78637], [2173, 78637], .contexts []⟩,
    ⟨[2173, 78637], [2173, 78637], .contexts []⟩,
    ⟨[77191, 1], [77191, 1], .contexts []⟩,
    ⟨[78637], [78637], .contexts []⟩,
    ⟨[2173, 78637], [2173, 78637], .contexts [
        ⟨9021, false, false, [2173], []⟩
      ]⟩,
    ⟨[2173], [2173], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 141. -/
def y322TCContextRaw141 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2173], [2173], .contexts []⟩,
    ⟨[2173], [2173], .contexts [
        ⟨24, false, false, [], [2173]⟩,
        ⟨9023, false, false, [], []⟩,
        ⟨9024, false, false, [], []⟩
      ]⟩,
    ⟨[2173, 78637], [2173, 78637], .contexts [
        ⟨9025, true, false, [], [78637]⟩
      ]⟩,
    ⟨[77191, 1], [2173, 78637], .contexts [
        ⟨9020, false, false, [], []⟩,
        ⟨3480, true, false, [], [1]⟩,
        ⟨256, false, false, [77193], []⟩,
        ⟨257, false, false, [77193], []⟩,
        ⟨553, false, false, [], [5]⟩,
        ⟨655, false, false, [], [5]⟩,
        ⟨558, false, false, [], [5]⟩,
        ⟨558, false, false, [], [5]⟩,
        ⟨9017, false, false, [], []⟩,
        ⟨9018, false, false, [], []⟩,
        ⟨9019, false, false, [], []⟩,
        ⟨9019, false, false, [], []⟩,
        ⟨9022, false, false, [], []⟩,
        ⟨9026, false, false, [], []⟩
      ]⟩,
    ⟨[575, 77195], [575, 77195], .contexts []⟩,
    ⟨[2175], [575, 2173], .source 1152⟩,
    ⟨[2173, 78637, 3], [2173, 78635], .contexts [
        ⟨8681, false, false, [2173], []⟩
      ]⟩,
    ⟨[2173, 78635], [2173, 78635], .contexts []⟩,
    ⟨[2173, 78635], [2173, 78635], .contexts []⟩,
    ⟨[2173, 78635], [2173, 78635], .contexts []⟩,
    ⟨[78635, 5], [78635, 5], .contexts []⟩,
    ⟨[78635], [78635], .contexts []⟩,
    ⟨[2177], [2174], .source 1153⟩,
    ⟨[2179], [2177, 2173], .source 1154⟩,
    ⟨[78635, 5], [2179, 78635], .contexts [
        ⟨9034, false, false, [], []⟩,
        ⟨8681, true, false, [], [5]⟩,
        ⟨9029, false, false, [2174], [78637, 3, 5]⟩,
        ⟨9016, true, false, [2174, 575], [3, 5]⟩,
        ⟨9028, true, false, [2174], [5, 3, 5]⟩,
        ⟨9028, true, false, [2174], [5, 3, 5]⟩,
        ⟨2952, true, false, [2174], [5, 3, 5]⟩,
        ⟨2948, true, false, [2174], [5, 3, 5]⟩,
        ⟨4744, false, false, [2174, 77195], []⟩,
        ⟨766, false, false, [2174, 77195], []⟩,
        ⟨9017, false, false, [2174], [3]⟩,
        ⟨9018, false, false, [2174], [3]⟩,
        ⟨9019, false, false, [2174], [3]⟩,
        ⟨9019, false, false, [2174], [3]⟩,
        ⟨9030, false, false, [2174], []⟩,
        ⟨9031, false, false, [2174], []⟩,
        ⟨9032, false, false, [2174], []⟩,
        ⟨9033, false, false, [2174], []⟩,
        ⟨9035, false, false, [2174, 2173], []⟩,
        ⟨9036, true, false, [], [2173, 78635]⟩,
        ⟨9037, true, false, [], [78635]⟩
      ]⟩,
    ⟨[77191, 1], [2173, 78637], .contexts [
        ⟨9027, false, false, [], []⟩
      ]⟩,
    ⟨[2173, 78633], [2173, 78633], .contexts []⟩,
    ⟨[2173, 78633], [2173, 78633], .contexts []⟩,
    ⟨[78633, 3], [78633, 3], .contexts []⟩,
    ⟨[77187], [77187], .contexts []⟩,
    ⟨[2172], [2172], .contexts []⟩,
    ⟨[2171], [2172], .contexts [
        ⟨9011, false, false, [], []⟩,
        ⟨9044, false, false, [], []⟩,
        ⟨9044, false, false, [], []⟩
      ]⟩,
    ⟨[78633, 3], [2171, 77187], .contexts [
        ⟨9042, false, false, [], []⟩,
        ⟨9041, true, false, [2172], [3]⟩,
        ⟨9040, true, false, [2172], [3]⟩,
        ⟨8677, true, false, [], [3]⟩,
        ⟨9033, true, false, [2172], [1, 3]⟩,
        ⟨9032, true, false, [2172], [1, 3]⟩,
        ⟨9031, true, false, [2172], [1, 3]⟩,
        ⟨9030, true, false, [2172], [1, 3]⟩,
        ⟨9019, true, false, [2172], [3, 1, 3]⟩,
        ⟨9019, true, false, [2172], [3, 1, 3]⟩,
        ⟨9018, true, false, [2172], [3, 1, 3]⟩,
        ⟨9039, true, false, [2172], [3, 1, 3]⟩,
        ⟨9020, true, false, [2172], [3, 1, 3]⟩,
        ⟨852, false, false, [2172, 77191], []⟩,
        ⟨853, false, false, [2172, 77191], []⟩,
        ⟨3499, false, false, [2172], [1]⟩,
        ⟨662, false, false, [2172], []⟩,
        ⟨663, false, false, [2172], []⟩,
        ⟨542, false, false, [2172], []⟩,
        ⟨542, false, false, [2172], []⟩,
        ⟨9043, false, false, [2172], []⟩,
        ⟨9045, true, false, [], [77187]⟩
      ]⟩,
    ⟨[77187, 3], [2173, 78633], .contexts [
        ⟨9046, true, false, [2170], [3]⟩,
        ⟨35, false, false, [2170, 78633], []⟩,
        ⟨9008, true, false, [], [78633]⟩
      ]⟩,
    ⟨[2179, 78635], [2179, 78635], .contexts []⟩,
    ⟨[78633, 5], [78633, 5], .contexts []⟩,
    ⟨[78633], [78633], .contexts []⟩,
    ⟨[2181], [2178], .source 1155⟩,
    ⟨[2178], [2178], .contexts []⟩,
    ⟨[2181], [2178], .contexts [
        ⟨9051, false, false, [], []⟩,
        ⟨9052, false, false, [], []⟩,
        ⟨9052, false, false, [], []⟩
      ]⟩,
    ⟨[78633, 5], [2181, 78633], .contexts [
        ⟨9049, false, false, [], []⟩,
        ⟨8677, true, false, [], [5]⟩,
        ⟨9048, true, false, [2178], [1, 5]⟩,
        ⟨9048, true, false, [2178], [1, 5]⟩,
        ⟨9038, true, false, [2178], [1, 5]⟩,
        ⟨9034, true, false, [2178], [1, 5]⟩,
        ⟨1509, false, false, [2178, 78635], []⟩,
        ⟨19, false, false, [2178, 78635], []⟩,
        ⟨8848, false, false, [2178], []⟩,
        ⟨8849, false, false, [2178], []⟩,
        ⟨8676, false, false, [2178], []⟩,
        ⟨8676, false, false, [2178], []⟩,
        ⟨9050, false, false, [2178], []⟩,
        ⟨9053, true, false, [], [78633]⟩
      ]⟩,
    ⟨[2171, 77187], [2171, 77187], .contexts []⟩,
    ⟨[78633, 15], [78631], .contexts [
        ⟨8851, false, false, [], []⟩,
        ⟨8852, false, false, [], []⟩,
        ⟨8672, false, false, [], []⟩,
        ⟨8672, false, false, [], []⟩
      ]⟩,
    ⟨[78633, 14], [78633, 15], .contexts [
        ⟨20, false, false, [78633], []⟩
      ]⟩,
    ⟨[77185, 3], [77185, 3], .contexts []⟩,
    ⟨[78631], [78631], .contexts []⟩,
    ⟨[77185, 3], [2173, 78631], .contexts [
        ⟨9058, false, false, [], []⟩,
        ⟨539, true, false, [], [3]⟩,
        ⟨9055, true, false, [2170], [15, 3]⟩,
        ⟨9055, true, false, [2170], [15, 3]⟩,
        ⟨9046, true, false, [2170], [15, 3]⟩,
        ⟨9042, true, false, [2170], [15, 3]⟩,
        ⟨900, false, false, [2170, 78633], []⟩,
        ⟨9057, false, false, [2170], []⟩,
        ⟨9056, false, false, [2170], []⟩,
        ⟨9059, false, false, [2170], []⟩,
        ⟨9015, true, false, [], [78631]⟩,
        ⟨9015, true, false, [], [78631]⟩,
        ⟨9009, true, false, [], [78631]⟩
      ]⟩,
    ⟨[2181, 78633], [2181, 78633], .contexts []⟩,
    ⟨[78631, 5], [78631, 5], .contexts []⟩,
    ⟨[2179], [2180], .contexts [
        ⟨9051, true, true, [], []⟩
      ]⟩,
    ⟨[2179], [2179], .contexts []⟩,
    ⟨[2180], [2180], .contexts []⟩,
    ⟨[2179], [2180], .contexts [
        ⟨9064, false, false, [], []⟩,
        ⟨9063, false, false, [], []⟩,
        ⟨9065, false, false, [], []⟩,
        ⟨9065, false, false, [], []⟩
      ]⟩,
    ⟨[77185, 3], [2173, 78631], .contexts [
        ⟨9060, false, false, [], []⟩
      ]⟩,
    ⟨[2173, 78631], [2173, 78631], .contexts []⟩,
    ⟨[2173, 78631], [2173, 78631], .contexts []⟩,
    ⟨[2173, 78631, 13], [2173, 78629], .contexts [
        ⟨8669, false, false, [2173], []⟩
      ]⟩,
    ⟨[2173, 78629], [2173, 78629], .contexts []⟩,
    ⟨[2173, 78629], [2173, 78629], .contexts []⟩,
    ⟨[77183], [77183], .contexts []⟩,
    ⟨[77183, 3], [2173, 78629], .contexts [
        ⟨9045, false, false, [2170], [77183, 3]⟩,
        ⟨9073, true, false, [2170, 2172], [3]⟩,
        ⟨535, true, false, [2170, 2172], [3]⟩,
        ⟨535, true, false, [2170, 2172], [3]⟩,
        ⟨666, true, false, [2170, 2172], [3]⟩,
        ⟨665, true, false, [2170, 2172], [3]⟩,
        ⟨108, true, false, [2170, 2172, 77185], [3]⟩,
        ⟨932, true, false, [2170, 2172, 77185], [3]⟩,
        ⟨9058, false, false, [2170, 2172], [13, 3, 3]⟩,
        ⟨9067, false, false, [2170, 2172], [13, 3, 3]⟩,
        ⟨9068, false, false, [2170, 2172], [13, 3, 3]⟩,
        ⟨9069, false, false, [2170, 2172], [13, 3, 3]⟩,
        ⟨9069, false, false, [2170, 2172], [13, 3, 3]⟩,
        ⟨9070, false, false, [2170, 2172], [3, 3]⟩,
        ⟨9071, false, false, [2170, 2172], [3, 3]⟩,
        ⟨9072, false, false, [2170, 2172], [3, 3]⟩,
        ⟨35, false, false, [2170, 78629], []⟩,
        ⟨9008, true, false, [], [78629]⟩
      ]⟩,
    ⟨[2179, 78631], [2179, 78631], .contexts []⟩,
    ⟨[78631, 5], [2179, 78631], .contexts [
        ⟨9062, false, false, [], []⟩,
        ⟨9062, false, false, [], []⟩,
        ⟨8673, true, false, [], [5]⟩,
        ⟨9061, true, false, [2180], [15, 5]⟩,
        ⟨9061, true, false, [2180], [15, 5]⟩,
        ⟨9054, true, false, [2180], [15, 5]⟩,
        ⟨9049, true, false, [2180], [15, 5]⟩,
        ⟨2006, false, false, [2180, 78633], []⟩,
        ⟨9057, false, false, [2180], []⟩,
        ⟨9056, false, false, [2180], []⟩,
        ⟨9059, false, false, [2180], []⟩,
        ⟨9066, true, false, [], [78631]⟩,
        ⟨9075, false, false, [], []⟩,
        ⟨9075, false, false, [], []⟩
      ]⟩,
    ⟨[78631, 13], [78629], .contexts [
        ⟨8853, false, false, [], []⟩
      ]⟩,
    ⟨[78629, 5], [78629, 5], .contexts []⟩,
    ⟨[2181, 78629], [2181, 78629], .contexts []⟩,
    ⟨[78629, 5, 1], [2181, 78627], .contexts [
        ⟨9078, false, false, [], [1]⟩,
        ⟨9078, false, false, [], [1]⟩,
        ⟨8669, true, false, [], [5, 1]⟩,
        ⟨9076, true, false, [2178], [13, 5, 1]⟩,
        ⟨1578, false, false, [2178, 78631], [1]⟩,
        ⟨108, false, false, [2178, 78631], [1]⟩,
        ⟨9077, false, false, [2178], [1]⟩,
        ⟨8854, false, false, [2178], [1]⟩,
        ⟨8668, false, false, [2178], [1]⟩,
        ⟨8668, false, false, [2178], [1]⟩,
        ⟨9053, true, false, [], [78629, 1]⟩,
        ⟨9079, false, false, [], [1]⟩,
        ⟨9079, false, false, [], [1]⟩,
        ⟨8665, false, false, [2181], []⟩
      ]⟩,
    ⟨[78627, 5], [78627, 5], .contexts []⟩,
    ⟨[78627], [78627], .contexts []⟩,
    ⟨[78627, 5], [2179, 78627], .contexts [
        ⟨9081, false, false, [], []⟩,
        ⟨9080, true, false, [2180], [5]⟩,
        ⟨1509, false, false, [2180, 78629], []⟩,
        ⟨19, false, false, [2180, 78629], []⟩,
        ⟨8855, false, false, [2180], []⟩,
        ⟨8856, false, false, [2180], []⟩,
        ⟨8664, false, false, [2180], []⟩,
        ⟨8664, false, false, [2180], []⟩,
        ⟨9082, false, false, [2180], []⟩,
        ⟨9066, true, false, [], [78627]⟩
      ]⟩,
    ⟨[2179, 78627], [2179, 78627], .contexts []⟩,
    ⟨[78627, 11], [78625], .contexts [
        ⟨8857, false, false, [], []⟩,
        ⟨8858, false, false, [], []⟩,
        ⟨8660, false, false, [], []⟩,
        ⟨8660, false, false, [], []⟩
      ]⟩,
    ⟨[78625, 5], [78625, 5], .contexts []⟩,
    ⟨[78625], [78625], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 142. -/
def y322TCContextRaw142 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78625, 5], [2181, 78625], .contexts [
        ⟨9086, false, false, [], []⟩,
        ⟨8661, true, false, [], [5]⟩,
        ⟨9084, true, false, [2178], [11, 5]⟩,
        ⟨9084, true, false, [2178], [11, 5]⟩,
        ⟨9083, true, false, [2178], [11, 5]⟩,
        ⟨9081, true, false, [2178], [11, 5]⟩,
        ⟨1645, false, false, [2178, 78627], []⟩,
        ⟨91, false, false, [2178, 78627], []⟩,
        ⟨9085, false, false, [2178], []⟩,
        ⟨9087, false, false, [2178], []⟩,
        ⟨9053, true, false, [], [78625]⟩
      ]⟩,
    ⟨[2181, 78625], [2181, 78625], .contexts []⟩,
    ⟨[2181, 78623], [2181, 78623], .contexts []⟩,
    ⟨[2181, 78623], [2181, 78623], .contexts []⟩,
    ⟨[78623, 5], [78623, 5], .contexts []⟩,
    ⟨[78623], [78623], .contexts []⟩,
    ⟨[2179, 78623], [2179, 78623], .contexts []⟩,
    ⟨[78623, 5], [2179, 78623], .contexts [
        ⟨9092, false, false, [], []⟩,
        ⟨9092, false, false, [], []⟩,
        ⟨9091, true, false, [2180], [5]⟩,
        ⟨9090, true, false, [2180], [5]⟩,
        ⟨8657, true, false, [], [5]⟩,
        ⟨9089, true, false, [2180], [9, 5]⟩,
        ⟨9089, true, false, [2180], [9, 5]⟩,
        ⟨9088, true, false, [2180], [9, 5]⟩,
        ⟨9086, true, false, [2180], [9, 5]⟩,
        ⟨1672, false, false, [2180, 78625], []⟩,
        ⟨77, false, false, [2180, 78625], []⟩,
        ⟨8859, false, false, [2180], []⟩,
        ⟨8860, false, false, [2180], []⟩,
        ⟨8656, false, false, [2180], []⟩,
        ⟨8656, false, false, [2180], []⟩,
        ⟨9093, false, false, [2180], []⟩,
        ⟨9066, true, false, [], [78623]⟩,
        ⟨9094, false, false, [], []⟩,
        ⟨9094, false, false, [], []⟩
      ]⟩,
    ⟨[2179, 78619], [2179, 78619], .contexts []⟩,
    ⟨[2179, 78619], [2179, 78619], .contexts []⟩,
    ⟨[78619, 1], [2181, 78623], .contexts [
        ⟨9097, true, false, [2178], [1]⟩,
        ⟨9096, true, false, [2178], [1]⟩,
        ⟨8650, true, false, [], [1]⟩,
        ⟨8653, true, false, [], [5, 1]⟩,
        ⟨9095, true, false, [2178], [1, 5, 1]⟩,
        ⟨1485, false, false, [2178, 78623], []⟩,
        ⟨9093, false, false, [2178], []⟩,
        ⟨9053, true, false, [], [78623]⟩
      ]⟩,
    ⟨[78717], [77137, 1], .source 39423⟩,
    ⟨[77137, 1], [78717], .contexts [
        ⟨9099, true, false, [], []⟩
      ]⟩,
    ⟨[78717, 1], [77137], .contexts [
        ⟨9100, true, false, [], [1]⟩,
        ⟨18, false, false, [77137], []⟩,
        ⟨457, false, false, [], []⟩
      ]⟩,
    ⟨[78717], [78717], .contexts []⟩,
    ⟨[78717], [78717], .contexts []⟩,
    ⟨[77137, 1], [78717], .contexts [
        ⟨9100, false, false, [], []⟩,
        ⟨9102, false, false, [], []⟩,
        ⟨9103, false, false, [], []⟩,
        ⟨9103, false, false, [], []⟩
      ]⟩,
    ⟨[78717, 5], [78717, 5], .contexts []⟩,
    ⟨[78717, 5], [77141], .contexts [
        ⟨9105, false, false, [], []⟩,
        ⟨9104, true, false, [], [5]⟩,
        ⟨165, false, false, [77137], []⟩,
        ⟨166, false, false, [77137], []⟩,
        ⟨4945, false, false, [], [1]⟩,
        ⟨459, false, false, [], []⟩,
        ⟨710, false, false, [], []⟩,
        ⟨463, false, false, [], []⟩,
        ⟨463, false, false, [], []⟩,
        ⟨8406, false, false, [], []⟩,
        ⟨1118, true, false, [], [77141]⟩
      ]⟩,
    ⟨[77137, 11], [1859, 78531], .contexts [
        ⟨8022, false, false, [], []⟩
      ]⟩,
    ⟨[1859, 78531], [1859, 78531], .contexts []⟩,
    ⟨[1859, 78531], [1859, 78531], .contexts []⟩,
    ⟨[2183], [1859, 1849], .source 1156⟩,
    ⟨[78717, 11], [78717, 11], .contexts []⟩,
    ⟨[2183, 77581], [2183, 77581], .contexts [
        ⟨8073, false, false, [2183], []⟩
      ]⟩,
    ⟨[2183, 77581], [2183, 77581], .contexts [
        ⟨24, true, false, [], [2183, 77581]⟩
      ]⟩,
    ⟨[78717, 11], [2183, 77581], .contexts [
        ⟨9111, false, false, [], []⟩,
        ⟨9104, true, false, [], [11]⟩,
        ⟨181, false, false, [77137], []⟩,
        ⟨182, false, false, [77137], []⟩,
        ⟨9107, false, false, [], [1]⟩,
        ⟨9108, false, false, [], [1]⟩,
        ⟨9109, false, false, [], [1]⟩,
        ⟨9109, false, false, [], [1]⟩,
        ⟨7875, false, false, [1859], []⟩,
        ⟨8051, false, false, [1859], []⟩,
        ⟨9110, true, false, [], [77581]⟩,
        ⟨9112, false, false, [], []⟩,
        ⟨9113, false, false, [], []⟩
      ]⟩,
    ⟨[2185], [2182], .source 1157⟩,
    ⟨[77137, 15], [1887, 78521], .contexts [
        ⟨8068, false, false, [], []⟩
      ]⟩,
    ⟨[1887, 78521], [1887, 78521], .contexts []⟩,
    ⟨[1887, 78521], [1887, 78521], .contexts []⟩,
    ⟨[77137, 15], [1887, 78521], .contexts [
        ⟨9116, false, false, [], []⟩,
        ⟨9117, false, false, [], []⟩,
        ⟨9118, false, false, [], []⟩,
        ⟨9118, false, false, [], []⟩
      ]⟩,
    ⟨[2187], [1887, 1899], .source 1158⟩,
    ⟨[78717, 15], [78717, 15], .contexts []⟩,
    ⟨[2187], [2187], .contexts []⟩,
    ⟨[2187], [2187], .contexts []⟩,
    ⟨[2187], [2187], .contexts [
        ⟨24, false, false, [], [2187]⟩,
        ⟨9122, false, false, [], []⟩,
        ⟨9123, false, false, [], []⟩
      ]⟩,
    ⟨[2189], [2186], .source 1159⟩,
    ⟨[78717, 11], [2183, 77581], .contexts [
        ⟨9114, false, false, [], []⟩
      ]⟩,
    ⟨[2183, 77581], [2183, 77581], .contexts []⟩,
    ⟨[2183, 77581], [2183, 77581], .contexts []⟩,
    ⟨[78717, 11], [2183, 77581], .contexts [
        ⟨9111, false, false, [], []⟩,
        ⟨9126, false, false, [], []⟩,
        ⟨9127, false, false, [], []⟩,
        ⟨9128, false, false, [], []⟩,
        ⟨9128, false, false, [], []⟩
      ]⟩,
    ⟨[2183, 77581, 13], [2183, 77579], .contexts [
        ⟨3113, false, false, [2183], []⟩
      ]⟩,
    ⟨[2183, 77579], [2183, 1895, 77577], .contexts [
        ⟨8083, false, false, [2183], []⟩
      ]⟩,
    ⟨[2183, 1895, 77577], [2183, 1895, 77577], .contexts []⟩,
    ⟨[2191], [2183, 1895], .source 1160⟩,
    ⟨[2183, 1895, 77577], [2191, 77577], .contexts [
        ⟨9133, true, false, [], [77577]⟩
      ]⟩,
    ⟨[2191, 77575], [2191, 77575], .contexts []⟩,
    ⟨[2191, 77575], [2191, 77575], .contexts []⟩,
    ⟨[2193], [2190], .source 1161⟩,
    ⟨[2190], [2190], .contexts []⟩,
    ⟨[2193], [2190], .contexts [
        ⟨9137, false, false, [], []⟩,
        ⟨9138, false, false, [], []⟩,
        ⟨9138, false, false, [], []⟩
      ]⟩,
    ⟨[2191], [2192], .contexts [
        ⟨9137, true, true, [], []⟩
      ]⟩,
    ⟨[78719], [78717, 3], .source 39424⟩,
    ⟨[78717, 3], [78719], .contexts [
        ⟨9141, true, false, [], []⟩
      ]⟩,
    ⟨[78719, 3], [78717], .contexts [
        ⟨9142, true, false, [], [3]⟩,
        ⟨35, false, false, [78717], []⟩,
        ⟨9103, false, false, [], []⟩
      ]⟩,
    ⟨[78719], [78719], .contexts []⟩,
    ⟨[78719], [78719], .contexts []⟩,
    ⟨[78717, 3], [78719], .contexts [
        ⟨9142, false, false, [], []⟩,
        ⟨9144, false, false, [], []⟩,
        ⟨9145, false, false, [], []⟩,
        ⟨9145, false, false, [], []⟩
      ]⟩,
    ⟨[78717, 1], [77137], .contexts [
        ⟨9101, false, false, [], []⟩
      ]⟩,
    ⟨[78719, 1], [78719, 1], .contexts []⟩,
    ⟨[78719, 1], [78545], .contexts [
        ⟨9148, false, false, [], []⟩,
        ⟨9146, true, false, [], [1]⟩,
        ⟨213, false, false, [78717], []⟩,
        ⟨216, false, false, [78717], []⟩,
        ⟨9147, false, false, [], [3, 1, 3]⟩,
        ⟨715, false, false, [], [3, 1, 3]⟩,
        ⟨457, false, false, [], [3, 1, 3]⟩,
        ⟨457, false, false, [], [3, 1, 3]⟩,
        ⟨716, false, false, [], [1, 3]⟩,
        ⟨717, false, false, [], [1, 3]⟩,
        ⟨453, false, false, [], [1, 3]⟩,
        ⟨453, false, false, [], [1, 3]⟩,
        ⟨718, false, false, [], [3]⟩,
        ⟨719, false, false, [], [3]⟩,
        ⟨449, false, false, [], [3]⟩,
        ⟨449, false, false, [], [3]⟩,
        ⟨8335, false, false, [], []⟩,
        ⟨8328, false, false, [], []⟩,
        ⟨8329, false, false, [], []⟩,
        ⟨8329, false, false, [], []⟩,
        ⟨8343, false, false, [], []⟩
      ]⟩,
    ⟨[78719, 1], [78545], .contexts [
        ⟨9149, false, false, [], []⟩,
        ⟨1118, true, false, [], [78545]⟩
      ]⟩,
    ⟨[78545, 1], [78719], .contexts [
        ⟨9150, true, false, [], [1]⟩,
        ⟨18, false, false, [78719], []⟩,
        ⟨9145, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 143. -/
def y322TCContextRaw143 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2195], [2183, 1461], .source 1162⟩,
    ⟨[78719, 11], [78719, 11], .contexts []⟩,
    ⟨[2195, 78243], [2195, 78243], .contexts [
        ⟨6692, false, false, [2195], []⟩
      ]⟩,
    ⟨[2195, 78243], [2195, 78243], .contexts [
        ⟨24, true, false, [], [2195, 78243]⟩
      ]⟩,
    ⟨[78719, 11], [2195, 78243], .contexts [
        ⟨9153, false, false, [], []⟩,
        ⟨9146, true, false, [], [11]⟩,
        ⟨231, false, false, [78717], []⟩,
        ⟨232, false, false, [78717], []⟩,
        ⟨9129, false, false, [], [3]⟩,
        ⟨6694, false, false, [2183], []⟩,
        ⟨9152, true, false, [], [78243]⟩,
        ⟨9154, false, false, [], []⟩,
        ⟨9155, false, false, [], []⟩
      ]⟩,
    ⟨[2197], [2194], .source 1163⟩,
    ⟨[2187, 77687], [2187, 77687], .contexts []⟩,
    ⟨[78717, 15], [2187, 77687], .contexts [
        ⟨9121, false, false, [], []⟩,
        ⟨9121, false, false, [], []⟩,
        ⟨9104, true, false, [], [15]⟩,
        ⟨199, false, false, [77137], []⟩,
        ⟨200, false, false, [77137], []⟩,
        ⟨9119, false, false, [], [1]⟩,
        ⟨8093, false, false, [1887], []⟩,
        ⟨9120, true, false, [], [77687]⟩,
        ⟨5587, false, false, [2187], []⟩,
        ⟨9124, true, false, [], [77687]⟩,
        ⟨9158, false, false, [], []⟩,
        ⟨9158, false, false, [], []⟩
      ]⟩,
    ⟨[2199], [2187, 1299], .source 1164⟩,
    ⟨[2199], [2199], .contexts []⟩,
    ⟨[2199], [2199], .contexts []⟩,
    ⟨[78719, 15], [2199, 77325], .contexts [
        ⟨9146, true, false, [], [15]⟩,
        ⟨245, false, false, [78717], []⟩,
        ⟨246, false, false, [78717], []⟩,
        ⟨9159, false, false, [], [3]⟩,
        ⟨5718, false, false, [2187], []⟩,
        ⟨9160, true, false, [], [77325]⟩,
        ⟨2655, false, false, [2199], []⟩,
        ⟨9162, true, false, [], [77325]⟩,
        ⟨9161, true, false, [], [77325]⟩,
        ⟨24, true, false, [], [2199, 77325]⟩
      ]⟩,
    ⟨[2201], [2198], .source 1165⟩,
    ⟨[1753, 77263], [1753, 77263], .contexts []⟩,
    ⟨[1753, 77263], [1753, 77263], .contexts []⟩,
    ⟨[77263, 5], [77263, 5], .contexts []⟩,
    ⟨[78719], [78719], .contexts []⟩,
    ⟨[1752], [1752], .contexts []⟩,
    ⟨[77263, 5], [1755, 78719], .contexts [
        ⟨9167, false, false, [], []⟩,
        ⟨9166, true, false, [1752], [5]⟩,
        ⟨9165, true, false, [1752], [5]⟩,
        ⟨1211, true, false, [], [5]⟩,
        ⟨8339, true, false, [1752], [1, 5]⟩,
        ⟨8339, true, false, [1752], [1, 5]⟩,
        ⟨8338, true, false, [1752], [1, 5]⟩,
        ⟨8352, true, false, [1752], [1, 5]⟩,
        ⟨8329, true, false, [1752], [5, 1, 5]⟩,
        ⟨8329, true, false, [1752], [5, 1, 5]⟩,
        ⟨8328, true, false, [1752], [5, 1, 5]⟩,
        ⟨9150, true, false, [1752], [5, 1, 5]⟩,
        ⟨9148, true, false, [1752], [5, 1, 5]⟩,
        ⟨1909, false, false, [1752, 78719], []⟩,
        ⟨9168, false, false, [1752], []⟩,
        ⟨9169, true, false, [], [78719]⟩,
        ⟨9169, true, false, [], [78719]⟩,
        ⟨8354, true, false, [], [78719]⟩
      ]⟩,
    ⟨[1753], [1754], .contexts [
        ⟨7545, true, true, [], []⟩
      ]⟩,
    ⟨[78719, 11], [2195, 78243], .contexts [
        ⟨9156, false, false, [], []⟩
      ]⟩,
    ⟨[2195, 78243], [2195, 78243], .contexts []⟩,
    ⟨[2195, 78243], [2195, 78243], .contexts []⟩,
    ⟨[2203], [1753, 277], .source 1166⟩,
    ⟨[78243, 5], [78243, 5], .contexts []⟩,
    ⟨[78281], [78281], .contexts []⟩,
    ⟨[2205], [2197, 2203], .source 1167⟩,
    ⟨[78243, 5], [2205, 78281], .contexts [
        ⟨9176, false, false, [], []⟩,
        ⟨9174, true, false, [2194], [5]⟩,
        ⟨9174, true, false, [2194], [5]⟩,
        ⟨9173, true, false, [2194], [5]⟩,
        ⟨9172, true, false, [2194], [5]⟩,
        ⟨9153, true, false, [2194], [5]⟩,
        ⟨1083, false, false, [2194, 78719], []⟩,
        ⟨1084, false, false, [2194, 78719], []⟩,
        ⟨9170, true, false, [2194, 1754], [5, 11]⟩,
        ⟨49, false, false, [2194, 1754, 77263], [11]⟩,
        ⟨9171, true, false, [2194], [77263, 11]⟩,
        ⟨9165, false, false, [2194], [11]⟩,
        ⟨9166, false, false, [2194], [11]⟩,
        ⟨9166, false, false, [2194], [11]⟩,
        ⟨6879, false, false, [2194, 1753], []⟩,
        ⟨9175, true, false, [2194], [78281]⟩,
        ⟨9177, false, false, [2194, 2203], []⟩,
        ⟨9157, true, false, [], [2203, 78281]⟩,
        ⟨9178, true, false, [], [78281]⟩
      ]⟩,
    ⟨[2207], [2204], .source 1168⟩,
    ⟨[77263, 5], [1755, 78719], .contexts [
        ⟨9170, false, false, [], []⟩
      ]⟩,
    ⟨[1755, 78719], [1755, 78719], .contexts []⟩,
    ⟨[1755, 78719], [1755, 78719], .contexts []⟩,
    ⟨[1755, 77141], [1755, 77141], .contexts []⟩,
    ⟨[1755, 77141], [1755, 77141], .contexts []⟩,
    ⟨[77263, 3], [77265], .contexts [
        ⟨2890, false, false, [], []⟩,
        ⟨1412, false, false, [], []⟩,
        ⟨1219, false, false, [], []⟩,
        ⟨1219, false, false, [], []⟩
      ]⟩,
    ⟨[77141, 3], [77141, 3], .contexts []⟩,
    ⟨[1754], [1754], .contexts []⟩,
    ⟨[77141, 3], [1753, 77267], .contexts [
        ⟨9187, false, false, [], []⟩,
        ⟨9185, true, false, [1754], [3]⟩,
        ⟨9184, true, false, [1754], [3]⟩,
        ⟨9106, true, false, [], [3]⟩,
        ⟨9143, true, false, [], [5, 3]⟩,
        ⟨9183, true, false, [1754], [3, 5, 3]⟩,
        ⟨9183, true, false, [1754], [3, 5, 3]⟩,
        ⟨9182, true, false, [1754], [3, 5, 3]⟩,
        ⟨9181, true, false, [1754], [3, 5, 3]⟩,
        ⟨9167, true, false, [1754], [3, 5, 3]⟩,
        ⟨2018, false, false, [1754, 77263], []⟩,
        ⟨265, false, false, [1754, 77263], []⟩,
        ⟨9186, false, false, [1754], [5]⟩,
        ⟨2903, false, false, [1754], []⟩,
        ⟨1410, false, false, [1754], []⟩,
        ⟨1223, false, false, [1754], []⟩,
        ⟨1223, false, false, [1754], []⟩,
        ⟨6909, false, false, [1754], []⟩,
        ⟨9188, true, false, [], [77267]⟩,
        ⟨9188, true, false, [], [77267]⟩,
        ⟨9171, true, false, [], [77267]⟩
      ]⟩,
    ⟨[1753, 77267], [1753, 77267], .contexts []⟩,
    ⟨[2209], [1753, 561], .source 1169⟩,
    ⟨[77141, 9], [77143], .contexts [
        ⟨462, false, false, [], []⟩
      ]⟩,
    ⟨[77271, 3], [77271, 3], .contexts []⟩,
    ⟨[2211], [2208], .source 1170⟩,
    ⟨[2208], [2208], .contexts []⟩,
    ⟨[77271, 3], [2211, 77143], .contexts [
        ⟨9193, false, false, [], []⟩,
        ⟨9191, false, false, [2208], [77271, 3]⟩,
        ⟨2905, true, false, [2208, 1753], [3]⟩,
        ⟨9190, true, false, [2208], [9, 3]⟩,
        ⟨9190, true, false, [2208], [9, 3]⟩,
        ⟨9189, true, false, [2208], [9, 3]⟩,
        ⟨9187, true, false, [2208], [9, 3]⟩,
        ⟨1010, false, false, [2208, 77141], []⟩,
        ⟨77, false, false, [2208, 77141], []⟩,
        ⟨9192, false, false, [2208], []⟩,
        ⟨708, false, false, [2208], []⟩,
        ⟨467, false, false, [2208], []⟩,
        ⟨467, false, false, [2208], []⟩,
        ⟨8440, false, false, [2208], []⟩,
        ⟨9195, true, false, [], [77143]⟩,
        ⟨9195, true, false, [], [77143]⟩,
        ⟨9194, true, false, [], [77143]⟩
      ]⟩,
    ⟨[2209], [2210], .contexts [
        ⟨9194, true, true, [], []⟩
      ]⟩,
    ⟨[2211, 77143], [2211, 77143], .contexts []⟩,
    ⟨[77271, 3], [2211, 77143], .contexts [
        ⟨9193, false, false, [], []⟩,
        ⟨9196, false, false, [], []⟩,
        ⟨9198, false, false, [], []⟩,
        ⟨9198, false, false, [], []⟩
      ]⟩,
    ⟨[2211, 77145], [2211, 77145], .contexts []⟩,
    ⟨[2211, 77145], [2211, 77145], .contexts []⟩,
    ⟨[77145, 3], [77145, 3], .contexts []⟩,
    ⟨[2210], [2210], .contexts []⟩,
    ⟨[77145, 3], [2209, 77273], .contexts [
        ⟨9202, false, false, [], []⟩,
        ⟨9201, true, false, [2210], [3]⟩,
        ⟨9200, true, false, [2210], [3]⟩,
        ⟨466, true, false, [], [3]⟩,
        ⟨9199, true, false, [2210], [11, 3]⟩,
        ⟨976, false, false, [2210, 77271], []⟩,
        ⟨91, false, false, [2210, 77271], []⟩,
        ⟨1229, false, false, [2210], []⟩,
        ⟨1405, false, false, [2210], []⟩,
        ⟨1233, false, false, [2210], []⟩,
        ⟨1233, false, false, [2210], []⟩,
        ⟨6923, false, false, [2210], []⟩,
        ⟨9203, true, false, [], [77273]⟩,
        ⟨9203, true, false, [], [77273]⟩,
        ⟨9197, true, false, [], [77273]⟩
      ]⟩,
    ⟨[77273, 3], [2211, 77145], .contexts [
        ⟨9204, true, false, [2208], [3]⟩,
        ⟨35, false, false, [2208, 77145], []⟩,
        ⟨9194, true, false, [], [77145]⟩
      ]⟩,
    ⟨[78721], [77135, 7], .source 39425⟩,
    ⟨[77135, 7], [78721], .contexts [
        ⟨9206, true, false, [], []⟩
      ]⟩,
    ⟨[78721], [78721], .contexts []⟩,
    ⟨[78721], [78721], .contexts []⟩,
    ⟨[77135, 7], [78721], .contexts [
        ⟨9207, false, false, [], []⟩,
        ⟨9208, false, false, [], []⟩,
        ⟨9209, false, false, [], []⟩,
        ⟨9209, false, false, [], []⟩
      ]⟩,
    ⟨[77135, 1], [77133], .contexts [
        ⟨718, false, false, [], []⟩,
        ⟨719, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩
      ]⟩,
    ⟨[77133, 7], [78551], .contexts [
        ⟨8377, false, false, [], []⟩
      ]⟩,
    ⟨[78551], [78551], .contexts []⟩,
    ⟨[78551], [78551], .contexts [
        ⟨1118, true, false, [], [78551]⟩
      ]⟩,
    ⟨[1075], [1075], .contexts [
        ⟨24, false, false, [], [1075]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 144. -/
def y322TCContextRaw144 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1423, 78257], [1423, 78257], .contexts []⟩,
    ⟨[77135, 15], [1423, 78257], .contexts [
        ⟨6680, false, false, [], []⟩,
        ⟨6682, false, false, [], []⟩,
        ⟨9216, false, false, [], []⟩,
        ⟨9216, false, false, [], []⟩
      ]⟩,
    ⟨[1423, 78539], [1423, 78539], .contexts []⟩,
    ⟨[1423, 78539], [1423, 78539], .contexts []⟩,
    ⟨[78539], [78539], .contexts []⟩,
    ⟨[1423, 78539], [1423, 78539], .contexts [
        ⟨9220, false, false, [1423], []⟩
      ]⟩,
    ⟨[1423], [1423], .contexts [
        ⟨24, false, false, [], [1423]⟩
      ]⟩,
    ⟨[1423, 78539], [1423, 78539], .contexts [
        ⟨9222, true, false, [], [78539]⟩
      ]⟩,
    ⟨[78721, 15], [1423, 78539], .contexts [
        ⟨9210, true, false, [], [15]⟩,
        ⟨1791, false, false, [77135], []⟩,
        ⟨1792, false, false, [77135], []⟩,
        ⟨9217, false, false, [], [7]⟩,
        ⟨8201, false, false, [1423], []⟩,
        ⟨9218, false, false, [], []⟩,
        ⟨9219, false, false, [], []⟩,
        ⟨9221, false, false, [], []⟩,
        ⟨9223, false, false, [], []⟩
      ]⟩,
    ⟨[78723], [77135, 9], .source 39426⟩,
    ⟨[77135, 9], [78723], .contexts [
        ⟨9225, true, false, [], []⟩
      ]⟩,
    ⟨[77135, 9], [78723], .contexts [
        ⟨9226, false, false, [], []⟩
      ]⟩,
    ⟨[78723], [78723], .contexts []⟩,
    ⟨[78723], [78723], .contexts []⟩,
    ⟨[77135, 9], [78723], .contexts [
        ⟨9227, false, false, [], []⟩,
        ⟨9228, false, false, [], []⟩,
        ⟨9229, false, false, [], []⟩,
        ⟨9229, false, false, [], []⟩
      ]⟩,
    ⟨[1063, 77133], [1063, 77133], .contexts []⟩,
    ⟨[78723], [78723], .contexts []⟩,
    ⟨[78723, 1], [1063, 78723], .contexts [
        ⟨9230, true, false, [], [1]⟩,
        ⟨1143, false, false, [77135], []⟩,
        ⟨1146, false, false, [77135], []⟩,
        ⟨9211, false, false, [], [9, 1, 9]⟩,
        ⟨4890, false, false, [], [1, 9]⟩,
        ⟨9231, false, false, [], [1, 9]⟩,
        ⟨9231, false, false, [], [1, 9]⟩,
        ⟨448, false, false, [1063], [9]⟩,
        ⟨9226, false, false, [1063], []⟩,
        ⟨9232, false, false, [1063], []⟩,
        ⟨5837, true, false, [], [78723]⟩
      ]⟩,
    ⟨[1859, 78533], [1859, 78533], .contexts []⟩,
    ⟨[2213], [1859, 1843], .source 1171⟩,
    ⟨[77135, 11, 9, 11], [2213, 1857, 77135], .contexts [
        ⟨8012, false, false, [], [9, 11]⟩,
        ⟨8015, false, false, [], [9, 11]⟩,
        ⟨9234, false, false, [], [9, 11]⟩,
        ⟨9234, false, false, [], [9, 11]⟩,
        ⟨7880, true, false, [1859], [9, 11]⟩,
        ⟨7967, true, false, [1859, 1830], [5, 9, 11]⟩,
        ⟨7982, true, false, [1859, 1830], [5, 9, 11]⟩,
        ⟨1034, false, false, [1859, 1830, 78535], [11]⟩,
        ⟨50, false, false, [1859, 1830, 78535], [11]⟩,
        ⟨7886, false, false, [1859, 1830], [11]⟩,
        ⟨7983, false, false, [1859, 1830], [11]⟩,
        ⟨7985, true, false, [1859], [78533, 11]⟩,
        ⟨7985, true, false, [1859], [78533, 11]⟩,
        ⟨7984, true, false, [1859], [78533, 11]⟩,
        ⟨9235, true, false, [], [78533, 11]⟩,
        ⟨8017, false, false, [2213], []⟩
      ]⟩,
    ⟨[2215], [2213, 1857], .source 1172⟩,
    ⟨[78723, 15], [1423, 78541], .contexts [
        ⟨9230, true, false, [], [15]⟩,
        ⟨323, false, false, [77135], []⟩,
        ⟨324, false, false, [77135], []⟩,
        ⟨9217, false, false, [], [9]⟩,
        ⟨8208, false, false, [1423], []⟩,
        ⟨8213, false, false, [1423], []⟩,
        ⟨9222, true, false, [], [78541]⟩
      ]⟩,
    ⟨[78725], [78545, 7], .source 39427⟩,
    ⟨[78725], [78725], .contexts []⟩,
    ⟨[78545, 7], [78725], .contexts [
        ⟨9239, true, false, [], []⟩,
        ⟨9240, false, false, [], []⟩,
        ⟨9240, false, false, [], []⟩
      ]⟩,
    ⟨[78725, 3], [78551], .contexts [
        ⟨9241, true, false, [], [3]⟩,
        ⟨1769, false, false, [78545], []⟩,
        ⟨1770, false, false, [78545], []⟩,
        ⟨8344, false, false, [], [7]⟩,
        ⟨9212, false, false, [], []⟩,
        ⟨8373, false, false, [], []⟩,
        ⟨8374, false, false, [], []⟩,
        ⟨8374, false, false, [], []⟩,
        ⟨9213, false, false, [], []⟩,
        ⟨9214, false, false, [], []⟩
      ]⟩,
    ⟨[78545, 15], [78407], .contexts [
        ⟨8327, true, false, [], [15]⟩,
        ⟨3, false, false, [78407], []⟩,
        ⟨7535, false, false, [], []⟩,
        ⟨7534, false, false, [], []⟩,
        ⟨7535, false, false, [], []⟩,
        ⟨7535, false, false, [], []⟩
      ]⟩,
    ⟨[78725, 15], [78543], .contexts [
        ⟨9241, true, false, [], [15]⟩,
        ⟨1791, false, false, [78545], []⟩,
        ⟨1792, false, false, [78545], []⟩,
        ⟨9243, false, false, [], [7]⟩,
        ⟨8321, false, false, [], []⟩,
        ⟨8322, false, false, [], []⟩,
        ⟨8323, false, false, [], []⟩,
        ⟨8323, false, false, [], []⟩,
        ⟨8324, false, false, [], []⟩,
        ⟨1118, true, false, [], [78543]⟩
      ]⟩,
    ⟨[78727], [78545, 11], .source 39428⟩,
    ⟨[78545, 11], [78727], .contexts [
        ⟨9245, true, false, [], []⟩
      ]⟩,
    ⟨[78727, 11], [78545], .contexts [
        ⟨9246, true, false, [], [11]⟩,
        ⟨90, false, false, [78545], []⟩,
        ⟨8329, false, false, [], []⟩
      ]⟩,
    ⟨[78727], [78727], .contexts []⟩,
    ⟨[78727], [78727], .contexts []⟩,
    ⟨[78545, 11], [78727], .contexts [
        ⟨9246, false, false, [], []⟩,
        ⟨9248, false, false, [], []⟩,
        ⟨9249, false, false, [], []⟩,
        ⟨9249, false, false, [], []⟩
      ]⟩,
    ⟨[78727, 1], [2195, 78243], .contexts [
        ⟨9250, true, false, [], [1]⟩,
        ⟨992, false, false, [78545], []⟩,
        ⟨993, false, false, [78545], []⟩,
        ⟨9151, false, false, [], [11]⟩,
        ⟨9144, false, false, [], [11]⟩,
        ⟨9145, false, false, [], [11]⟩,
        ⟨9145, false, false, [], [11]⟩,
        ⟨9172, false, false, [], []⟩,
        ⟨9173, false, false, [], []⟩,
        ⟨9174, false, false, [], []⟩,
        ⟨9174, false, false, [], []⟩,
        ⟨9154, false, false, [], []⟩,
        ⟨9155, false, false, [], []⟩
      ]⟩,
    ⟨[77133, 11], [1855, 78537], .contexts [
        ⟨8005, false, false, [], []⟩
      ]⟩,
    ⟨[1855, 78537], [1855, 78537], .contexts []⟩,
    ⟨[1855, 78537], [1855, 78537], .contexts []⟩,
    ⟨[78727, 3], [78727, 3], .contexts []⟩,
    ⟨[1855, 78537], [1855, 78537], .contexts [
        ⟨7974, false, false, [1855], []⟩
      ]⟩,
    ⟨[1855, 78537], [1855, 78537], .contexts [
        ⟨24, true, false, [], [1855, 78537]⟩
      ]⟩,
    ⟨[78727, 3], [1855, 78537], .contexts [
        ⟨9255, false, false, [], []⟩,
        ⟨9250, true, false, [], [3]⟩,
        ⟨335, false, false, [78545], []⟩,
        ⟨336, false, false, [78545], []⟩,
        ⟨8344, false, false, [], [11]⟩,
        ⟨9252, false, false, [], []⟩,
        ⟨9253, false, false, [], []⟩,
        ⟨9254, false, false, [], []⟩,
        ⟨9254, false, false, [], []⟩,
        ⟨9256, false, false, [], []⟩,
        ⟨9257, false, false, [], []⟩
      ]⟩,
    ⟨[1853], [1854], .contexts [
        ⟨8004, true, true, [], []⟩
      ]⟩,
    ⟨[78727, 5], [78727, 5], .contexts []⟩,
    ⟨[2217], [2202], .source 1173⟩,
    ⟨[78727, 15], [1279, 77329], .contexts [
        ⟨9250, true, false, [], [15]⟩,
        ⟨358, false, false, [78545], []⟩,
        ⟨359, false, false, [78545], []⟩,
        ⟨9243, false, false, [], [11]⟩,
        ⟨7555, false, false, [], []⟩,
        ⟨7549, false, false, [], []⟩,
        ⟨7550, false, false, [], []⟩,
        ⟨7550, false, false, [], []⟩,
        ⟨7552, false, false, [], []⟩,
        ⟨7553, false, false, [], []⟩
      ]⟩,
    ⟨[2219], [1855, 1825], .source 1174⟩,
    ⟨[2219, 77497], [2219, 77497], .contexts []⟩,
    ⟨[2219, 77497], [2219, 77497], .contexts []⟩,
    ⟨[78727], [78727], .contexts []⟩,
    ⟨[2221], [2218], .source 1175⟩,
    ⟨[2218], [2218], .contexts []⟩,
    ⟨[77497, 9], [2221, 78727], .contexts [
        ⟨9265, true, false, [2218], [9]⟩,
        ⟨9264, true, false, [2218], [9]⟩,
        ⟨2969, true, false, [], [9]⟩,
        ⟨9263, false, false, [2218], [77495, 3, 9]⟩,
        ⟨7958, true, false, [2218, 1855], [3, 9]⟩,
        ⟨9254, true, false, [2218], [9, 3, 9]⟩,
        ⟨9254, true, false, [2218], [9, 3, 9]⟩,
        ⟨9253, true, false, [2218], [9, 3, 9]⟩,
        ⟨9258, true, false, [2218], [9, 3, 9]⟩,
        ⟨9255, true, false, [2218], [9, 3, 9]⟩,
        ⟨2706, false, false, [2218, 78727], []⟩,
        ⟨9266, false, false, [2218], []⟩,
        ⟨9268, true, false, [], [78727]⟩,
        ⟨9268, true, false, [], [78727]⟩,
        ⟨9267, true, false, [], [78727]⟩
      ]⟩,
    ⟨[78727, 9], [2219, 77497], .contexts [
        ⟨9269, true, false, [2220], [9]⟩,
        ⟨76, false, false, [2220, 77497], []⟩,
        ⟨9267, false, true, [], [77497]⟩
      ]⟩,
    ⟨[2203, 78279], [2203, 78279], .contexts []⟩,
    ⟨[2203, 78279, 9], [78727, 9, 5], .contexts [
        ⟨9271, true, false, [], [9]⟩,
        ⟨9271, true, false, [], [9]⟩,
        ⟨24, false, false, [], [2203, 78279, 9]⟩,
        ⟨6866, true, false, [2203], [9]⟩,
        ⟨9175, false, false, [], [78279, 9]⟩,
        ⟨1664, false, false, [1753], [78279, 9]⟩,
        ⟨90, true, false, [1753, 274, 78279], [9]⟩,
        ⟨6870, false, false, [1753, 274], [11, 9]⟩,
        ⟨8353, true, false, [], [11, 9]⟩,
        ⟨1084, true, false, [78545], [9]⟩,
        ⟨1083, true, false, [78545], [9]⟩,
        ⟨9250, false, false, [], [5, 9]⟩,
        ⟨9260, true, false, [], [9]⟩,
        ⟨9260, true, false, [], [9]⟩,
        ⟨2076, false, false, [78727], []⟩,
        ⟨2077, false, false, [78727], []⟩
      ]⟩,
    ⟨[78279, 9], [78279, 9], .contexts []⟩,
    ⟨[2223], [2217, 2219], .source 1176⟩,
    ⟨[78279, 9], [2223, 77499], .contexts [
        ⟨9273, false, false, [], []⟩,
        ⟨9272, false, false, [2202], []⟩,
        ⟨9270, false, false, [2202], [5]⟩,
        ⟨9264, false, false, [2202], [5]⟩,
        ⟨9265, false, false, [2202], [5]⟩,
        ⟨9265, false, false, [2202], [5]⟩,
        ⟨2981, false, false, [2202, 2219], []⟩,
        ⟨2986, false, false, [2202, 2219], []⟩,
        ⟨9261, true, false, [], [2219, 77499]⟩,
        ⟨9274, true, false, [], [77499]⟩
      ]⟩,
    ⟨[2223, 77499], [2223, 77499], .contexts []⟩,
    ⟨[2223, 77499], [2223, 77499], .contexts []⟩,
    ⟨[2227], [2223, 765], .source 1178⟩,
    ⟨[2227, 77615], [2227, 77615], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 145. -/
def y322TCContextRaw145 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77615, 13], [77615, 13], .contexts []⟩,
    ⟨[2229], [2226], .source 1179⟩,
    ⟨[2226], [2226], .contexts []⟩,
    ⟨[77615, 13], [2229, 78279], .contexts [
        ⟨9280, false, false, [], []⟩,
        ⟨9279, true, false, [2226], [13]⟩,
        ⟨3736, true, false, [], [13]⟩,
        ⟨9278, false, false, [2226], [77613, 9, 13]⟩,
        ⟨3701, true, false, [2226, 2223], [9, 13]⟩,
        ⟨9277, true, false, [2226], [13, 9, 13]⟩,
        ⟨9277, true, false, [2226], [13, 9, 13]⟩,
        ⟨9276, true, false, [2226], [13, 9, 13]⟩,
        ⟨9275, true, false, [2226], [13, 9, 13]⟩,
        ⟨9273, true, false, [2226], [13, 9, 13]⟩,
        ⟨828, false, false, [2226, 78279], []⟩,
        ⟨6866, false, false, [2226], []⟩,
        ⟨9282, true, false, [], [78279]⟩,
        ⟨9282, true, false, [], [78279]⟩,
        ⟨9281, true, false, [], [78279]⟩
      ]⟩,
    ⟨[2229, 78279], [2229, 78279], .contexts []⟩,
    ⟨[2231], [2229, 275], .source 1180⟩,
    ⟨[2233], [2231, 1985], .source 1181⟩,
    ⟨[13, 11, 13, 11], [], .contexts [
        ⟨136, false, false, [], []⟩
      ]⟩,
    ⟨[2235], [2232], .source 1182⟩,
    ⟨[2232], [2232], .contexts []⟩,
    ⟨[77873, 11], [2235, 77615], .contexts [
        ⟨9286, false, false, [2232], [77873, 11]⟩,
        ⟨8356, true, false, [2232, 2231], [11]⟩,
        ⟨9285, false, false, [2232], [77261, 13, 11]⟩,
        ⟨6870, true, false, [2232, 2229], [13, 11]⟩,
        ⟨9284, true, false, [2232], [11, 13, 11]⟩,
        ⟨9284, true, false, [2232], [11, 13, 11]⟩,
        ⟨9283, true, false, [2232], [11, 13, 11]⟩,
        ⟨9280, true, false, [2232], [11, 13, 11]⟩,
        ⟨9287, false, false, [2232, 77615], []⟩,
        ⟨3739, false, false, [2232], []⟩,
        ⟨9289, true, false, [], [77615]⟩,
        ⟨9289, true, false, [], [77615]⟩,
        ⟨9288, true, false, [], [77615]⟩
      ]⟩,
    ⟨[2233], [2234], .contexts [
        ⟨9288, true, true, [], []⟩
      ]⟩,
    ⟨[77873], [2235, 77617], .contexts [
        ⟨9291, false, false, [2232], [77873]⟩,
        ⟨90, true, false, [2232, 2234, 77873], []⟩,
        ⟨9290, false, false, [2232, 2234], [11]⟩,
        ⟨3741, false, false, [2232], []⟩,
        ⟨3743, false, false, [2232], []⟩,
        ⟨3744, false, false, [2232], []⟩,
        ⟨3744, false, false, [2232], []⟩,
        ⟨9288, true, false, [], [77617]⟩
      ]⟩,
    ⟨[2233], [2234], .contexts [
        ⟨9291, false, false, [], []⟩
      ]⟩,
    ⟨[2234], [2234], .contexts []⟩,
    ⟨[2233], [2234], .contexts [
        ⟨9293, false, false, [], []⟩,
        ⟨9294, false, false, [], []⟩,
        ⟨9294, false, false, [], []⟩
      ]⟩,
    ⟨[77617, 5], [2233, 77871], .contexts [
        ⟨9292, true, false, [2234], [5]⟩,
        ⟨4963, false, false, [2234], []⟩,
        ⟨4952, false, false, [2234], []⟩,
        ⟨9295, true, false, [], [77871]⟩
      ]⟩,
    ⟨[77873], [2235, 77617], .contexts [
        ⟨9292, false, false, [], []⟩
      ]⟩,
    ⟨[2237], [2233, 1987], .source 1183⟩,
    ⟨[77617, 13], [2237, 77261], .contexts [
        ⟨9292, true, false, [2234], [13]⟩,
        ⟨8356, true, false, [2234, 1984], [13]⟩,
        ⟨98, false, false, [2234, 1984, 77261], []⟩,
        ⟨8357, true, false, [2234], [77261]⟩,
        ⟨9291, true, false, [], [1987, 77261]⟩,
        ⟨9298, true, false, [], [77261]⟩
      ]⟩,
    ⟨[2235, 77619], [2235, 77619], .contexts []⟩,
    ⟨[77875], [2235, 77619], .contexts [
        ⟨9293, false, false, [2232], [77875]⟩,
        ⟨24, false, false, [2232, 2234], [77875]⟩,
        ⟨4971, true, false, [2232, 2234], []⟩,
        ⟨9297, false, false, [2232, 2234], [1]⟩,
        ⟨3746, false, false, [2232], []⟩,
        ⟨9300, false, false, [2232, 2234], []⟩,
        ⟨9288, true, false, [], [77619]⟩
      ]⟩,
    ⟨[77619, 9], [2233, 77877], .contexts [
        ⟨9301, true, false, [2234], [9]⟩,
        ⟨4974, false, false, [2234], []⟩,
        ⟨4976, false, false, [2234], []⟩,
        ⟨9295, true, false, [], [77877]⟩
      ]⟩,
    ⟨[78729], [78551, 5], .source 39429⟩,
    ⟨[78729], [78729], .contexts []⟩,
    ⟨[78729], [78729], .contexts []⟩,
    ⟨[78551, 7], [77133], .contexts [
        ⟨8375, false, false, [], []⟩,
        ⟨8376, false, false, [], []⟩,
        ⟨719, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩,
        ⟨449, false, false, [], []⟩
      ]⟩,
    ⟨[78551, 15], [78413], .contexts [
        ⟨8372, true, false, [], [15]⟩,
        ⟨3, false, false, [78413], []⟩,
        ⟨7674, false, false, [], []⟩,
        ⟨7673, false, false, [], []⟩,
        ⟨7674, false, false, [], []⟩,
        ⟨7674, false, false, [], []⟩
      ]⟩,
    ⟨[78731], [78551, 11], .source 39430⟩,
    ⟨[78731], [78731], .contexts []⟩,
    ⟨[78551, 11], [78731], .contexts [
        ⟨9308, true, false, [], []⟩,
        ⟨9309, false, false, [], []⟩,
        ⟨9309, false, false, [], []⟩
      ]⟩,
    ⟨[78733], [78551, 13], .source 39431⟩,
    ⟨[78551, 13], [78733], .contexts [
        ⟨9311, true, false, [], []⟩
      ]⟩,
    ⟨[78733], [78733], .contexts []⟩,
    ⟨[78733, 7], [539, 77869], .contexts [
        ⟨9313, true, false, [], [7]⟩,
        ⟨9313, true, false, [], [7]⟩,
        ⟨9312, true, false, [], [7]⟩,
        ⟨124, false, false, [78551], []⟩,
        ⟨125, false, false, [78551], []⟩,
        ⟨9306, false, false, [], [13]⟩,
        ⟨8345, false, false, [], []⟩,
        ⟨8346, false, false, [], []⟩,
        ⟨8347, false, false, [], []⟩,
        ⟨8347, false, false, [], []⟩,
        ⟨4919, false, false, [539], []⟩,
        ⟨5823, true, false, [], [77869]⟩
      ]⟩,
    ⟨[77869, 7], [537, 78733], .contexts [
        ⟨9314, true, false, [538], [7]⟩,
        ⟨62, false, false, [538, 78733], []⟩,
        ⟨2792, true, false, [], [78733]⟩
      ]⟩,
    ⟨[78735], [77137, 7], .source 39432⟩,
    ⟨[77137, 7], [78735], .contexts [
        ⟨9316, true, false, [], []⟩
      ]⟩,
    ⟨[78735], [78735], .contexts []⟩,
    ⟨[78735], [78735], .contexts []⟩,
    ⟨[77137, 3], [77135], .contexts [
        ⟨716, false, false, [], []⟩,
        ⟨717, false, false, [], []⟩,
        ⟨453, false, false, [], []⟩,
        ⟨453, false, false, [], []⟩
      ]⟩,
    ⟨[78735, 3], [78735, 3], .contexts []⟩,
    ⟨[78737], [77137, 9], .source 39433⟩,
    ⟨[77137, 9], [78737], .contexts [
        ⟨9322, true, false, [], []⟩
      ]⟩,
    ⟨[77137, 9], [78737], .contexts [
        ⟨9323, false, false, [], []⟩
      ]⟩,
    ⟨[78737], [78737], .contexts []⟩,
    ⟨[78737], [78737], .contexts []⟩,
    ⟨[77137, 9], [78737], .contexts [
        ⟨9324, false, false, [], []⟩,
        ⟨9325, false, false, [], []⟩,
        ⟨9326, false, false, [], []⟩,
        ⟨9326, false, false, [], []⟩
      ]⟩,
    ⟨[78737], [78737], .contexts []⟩,
    ⟨[1077, 78737], [1077, 78737], .contexts []⟩,
    ⟨[1077, 78737], [1077, 78737], .contexts []⟩,
    ⟨[78737, 13], [78737, 13], .contexts []⟩,
    ⟨[1887, 78519], [1887, 78519], .contexts []⟩,
    ⟨[1887, 78519], [1887, 78519], .contexts []⟩,
    ⟨[1887, 78519], [1887, 78519], .contexts [
        ⟨8107, false, false, [1887], []⟩
      ]⟩,
    ⟨[1887], [1887], .contexts []⟩,
    ⟨[1887], [1887], .contexts []⟩,
    ⟨[1887], [1887], .contexts [
        ⟨24, false, false, [], [1887]⟩,
        ⟨9335, false, false, [], []⟩,
        ⟨9336, false, false, [], []⟩
      ]⟩,
    ⟨[1887, 78519], [1887, 78519], .contexts [
        ⟨9337, true, false, [], [78519]⟩
      ]⟩,
    ⟨[78737, 15], [1887, 78519], .contexts [
        ⟨9327, true, false, [], [15]⟩,
        ⟨323, false, false, [77137], []⟩,
        ⟨324, false, false, [77137], []⟩,
        ⟨9119, false, false, [], [9]⟩,
        ⟨7859, false, false, [1887], []⟩,
        ⟨9332, false, false, [], []⟩,
        ⟨9333, false, false, [], []⟩,
        ⟨9334, false, false, [], []⟩,
        ⟨9338, false, false, [], []⟩
      ]⟩,
    ⟨[1885], [1886], .contexts [
        ⟨8067, true, true, [], []⟩
      ]⟩,
    ⟨[78745], [77263, 9], .source 39437⟩,
    ⟨[77263, 9], [78745], .contexts [
        ⟨9341, true, false, [], []⟩
      ]⟩,
    ⟨[78745, 9], [77263], .contexts [
        ⟨9342, true, false, [], [9]⟩,
        ⟨76, false, false, [77263], []⟩,
        ⟨1216, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 146. -/
def y322TCContextRaw146 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77263, 9], [78745], .contexts [
        ⟨9342, false, false, [], []⟩
      ]⟩,
    ⟨[78745], [78745], .contexts []⟩,
    ⟨[78745], [78745], .contexts []⟩,
    ⟨[283, 77261], [283, 77261], .contexts []⟩,
    ⟨[283, 77261], [283, 77261], .contexts []⟩,
    ⟨[283, 77263], [283, 77263], .contexts []⟩,
    ⟨[283, 77263], [283, 77263], .contexts []⟩,
    ⟨[283, 77263], [283, 77263], .contexts []⟩,
    ⟨[283, 78745], [283, 78745], .contexts []⟩,
    ⟨[283, 78745], [283, 78745], .contexts []⟩,
    ⟨[283, 78745], [283, 78745], .contexts []⟩,
    ⟨[78745, 1], [78745, 1], .contexts []⟩,
    ⟨[78745, 1], [283, 78745], .contexts [
        ⟨9355, false, false, [], []⟩,
        ⟨9346, true, false, [], [1]⟩,
        ⟨9346, true, false, [], [1]⟩,
        ⟨9345, true, false, [], [1]⟩,
        ⟨9344, true, false, [], [1]⟩,
        ⟨1143, false, false, [77263], []⟩,
        ⟨1146, false, false, [77263], []⟩,
        ⟨1415, false, false, [], [9, 1, 9]⟩,
        ⟨1416, false, false, [], [9, 1, 9]⟩,
        ⟨1212, false, false, [], [9, 1, 9]⟩,
        ⟨1212, false, false, [], [9, 1, 9]⟩,
        ⟨1758, false, false, [], [1, 9]⟩,
        ⟨9347, false, false, [], [1, 9]⟩,
        ⟨9348, false, false, [], [1, 9]⟩,
        ⟨9348, false, false, [], [1, 9]⟩,
        ⟨1211, false, false, [283], [9]⟩,
        ⟨9349, false, false, [], [9]⟩,
        ⟨9350, false, false, [], [9]⟩,
        ⟨9351, false, false, [], [9]⟩,
        ⟨9342, false, false, [283], []⟩,
        ⟨9352, false, false, [], []⟩,
        ⟨9353, false, false, [], []⟩,
        ⟨9354, false, false, [], []⟩
      ]⟩,
    ⟨[283], [283], .contexts [
        ⟨24, false, false, [], [283]⟩
      ]⟩,
    ⟨[78745, 1], [283, 78745], .contexts [
        ⟨9356, false, false, [], []⟩,
        ⟨9357, true, false, [], [78745]⟩
      ]⟩,
    ⟨[78747], [78745, 11], .source 39438⟩,
    ⟨[78745, 11], [78747], .contexts [
        ⟨9359, true, false, [], []⟩
      ]⟩,
    ⟨[78745, 11], [78747], .contexts [
        ⟨9360, false, false, [], []⟩
      ]⟩,
    ⟨[78747], [78747], .contexts []⟩,
    ⟨[78747], [78747], .contexts []⟩,
    ⟨[78745, 11], [78747], .contexts [
        ⟨9361, false, false, [], []⟩,
        ⟨9362, false, false, [], []⟩,
        ⟨9363, false, false, [], []⟩,
        ⟨9363, false, false, [], []⟩
      ]⟩,
    ⟨[78745, 1], [283, 78745], .contexts [
        ⟨9355, false, false, [], []⟩,
        ⟨9358, false, false, [], []⟩,
        ⟨9352, false, false, [], []⟩,
        ⟨9354, false, false, [], []⟩,
        ⟨9354, false, false, [], []⟩
      ]⟩,
    ⟨[283, 78747], [283, 78747], .contexts []⟩,
    ⟨[283, 78747], [283, 78747], .contexts []⟩,
    ⟨[78747], [78747], .contexts []⟩,
    ⟨[78747, 1], [283, 78747], .contexts [
        ⟨9364, true, false, [], [1]⟩,
        ⟨992, false, false, [78745], []⟩,
        ⟨993, false, false, [78745], []⟩,
        ⟨9365, false, false, [], [11]⟩,
        ⟨9360, false, false, [283], []⟩,
        ⟨9366, false, false, [], []⟩,
        ⟨9367, false, false, [], []⟩,
        ⟨9368, false, false, [283], []⟩,
        ⟨9357, true, false, [], [78747]⟩
      ]⟩,
    ⟨[78749], [78747, 13], .source 39439⟩,
    ⟨[78747, 13], [78749], .contexts [
        ⟨9370, true, false, [], []⟩
      ]⟩,
    ⟨[78751], [78749, 15], .source 39440⟩,
    ⟨[78749, 15], [78751], .contexts [
        ⟨9372, true, false, [], []⟩
      ]⟩,
    ⟨[78749], [78749], .contexts []⟩,
    ⟨[78753], [78751, 1], .source 39441⟩,
    ⟨[78751, 1], [78753], .contexts [
        ⟨9375, true, false, [], []⟩
      ]⟩,
    ⟨[78751], [78751], .contexts []⟩,
    ⟨[78755], [78753, 3], .source 39442⟩,
    ⟨[78753, 3], [78755], .contexts [
        ⟨9378, true, false, [], []⟩
      ]⟩,
    ⟨[78753], [78753], .contexts []⟩,
    ⟨[78757], [78755, 5], .source 39443⟩,
    ⟨[78755], [78755], .contexts []⟩,
    ⟨[78759], [78757, 1], .source 39444⟩,
    ⟨[78757], [78757], .contexts []⟩,
    ⟨[78761], [78759, 9], .source 39445⟩,
    ⟨[78759], [78759], .contexts []⟩,
    ⟨[78763], [78761, 11], .source 39446⟩,
    ⟨[78761], [78761], .contexts []⟩,
    ⟨[78765], [78763, 1], .source 39447⟩,
    ⟨[78763], [78763], .contexts []⟩,
    ⟨[78767], [78765, 13], .source 39448⟩,
    ⟨[78765], [78765], .contexts []⟩,
    ⟨[78769], [78767, 15], .source 39449⟩,
    ⟨[78767], [78767], .contexts []⟩,
    ⟨[78771], [78769, 1], .source 39450⟩,
    ⟨[78769], [78769], .contexts []⟩,
    ⟨[78773], [78771, 3], .source 39451⟩,
    ⟨[78771], [78771], .contexts []⟩,
    ⟨[78775], [78773, 5], .source 39452⟩,
    ⟨[78773], [78773], .contexts []⟩,
    ⟨[78777], [78775, 1], .source 39453⟩,
    ⟨[78775], [78775], .contexts []⟩,
    ⟨[78779], [78777, 9], .source 39454⟩,
    ⟨[78777], [78777], .contexts []⟩,
    ⟨[78781], [78779, 11], .source 39455⟩,
    ⟨[78779, 11], [78781], .contexts [
        ⟨9405, true, false, [], []⟩
      ]⟩,
    ⟨[78779], [78779], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 147. -/
def y322TCContextRaw147 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78781, 11], [78779], .contexts [
        ⟨9406, true, false, [], [11]⟩,
        ⟨90, false, false, [78779], []⟩,
        ⟨9407, false, false, [], []⟩
      ]⟩,
    ⟨[78783], [78781, 1], .source 39456⟩,
    ⟨[78781, 1], [78783], .contexts [
        ⟨9409, true, false, [], []⟩
      ]⟩,
    ⟨[78781], [78781], .contexts []⟩,
    ⟨[78783, 1], [78781], .contexts [
        ⟨9410, true, false, [], [1]⟩,
        ⟨18, false, false, [78781], []⟩,
        ⟨9411, false, false, [], []⟩
      ]⟩,
    ⟨[78785], [78783, 13], .source 39457⟩,
    ⟨[78783, 13], [78785], .contexts [
        ⟨9413, true, false, [], []⟩
      ]⟩,
    ⟨[78783], [78783], .contexts []⟩,
    ⟨[78785, 13], [78783], .contexts [
        ⟨9414, true, false, [], [13]⟩,
        ⟨98, false, false, [78783], []⟩,
        ⟨9415, false, false, [], []⟩
      ]⟩,
    ⟨[78787], [78785, 15], .source 39458⟩,
    ⟨[78785, 15], [78787], .contexts [
        ⟨9417, true, false, [], []⟩
      ]⟩,
    ⟨[78785], [78785], .contexts []⟩,
    ⟨[78787, 15], [78785], .contexts [
        ⟨9418, true, false, [], [15]⟩,
        ⟨3, false, false, [78785], []⟩,
        ⟨9419, false, false, [], []⟩
      ]⟩,
    ⟨[78789], [78787, 1], .source 39459⟩,
    ⟨[78787, 1], [78789], .contexts [
        ⟨9421, true, false, [], []⟩
      ]⟩,
    ⟨[78787], [78787], .contexts []⟩,
    ⟨[78789, 1], [78787], .contexts [
        ⟨9422, true, false, [], [1]⟩,
        ⟨18, false, false, [78787], []⟩,
        ⟨9423, false, false, [], []⟩
      ]⟩,
    ⟨[78791], [78789, 3], .source 39460⟩,
    ⟨[78789], [78789], .contexts []⟩,
    ⟨[78791, 3], [78789], .contexts [
        ⟨9425, false, false, [], [3]⟩,
        ⟨35, false, false, [78789], []⟩,
        ⟨9426, false, false, [], []⟩
      ]⟩,
    ⟨[78793], [78791, 5], .source 39461⟩,
    ⟨[78791], [78791], .contexts []⟩,
    ⟨[78793, 5], [78791], .contexts [
        ⟨9428, false, false, [], [5]⟩,
        ⟨49, false, false, [78791], []⟩,
        ⟨9429, false, false, [], []⟩
      ]⟩,
    ⟨[78795], [78793, 1], .source 39462⟩,
    ⟨[78793], [78793], .contexts []⟩,
    ⟨[78795, 1], [78793], .contexts [
        ⟨9431, false, false, [], [1]⟩,
        ⟨18, false, false, [78793], []⟩,
        ⟨9432, false, false, [], []⟩
      ]⟩,
    ⟨[78797], [78795, 9], .source 39463⟩,
    ⟨[78795, 9], [78797], .contexts [
        ⟨9434, true, false, [], []⟩
      ]⟩,
    ⟨[78795], [78795], .contexts []⟩,
    ⟨[78797, 9], [78795], .contexts [
        ⟨9435, true, false, [], [9]⟩,
        ⟨76, false, false, [78795], []⟩,
        ⟨9436, false, false, [], []⟩
      ]⟩,
    ⟨[78799], [78797, 11], .source 39464⟩,
    ⟨[78797, 11], [78799], .contexts [
        ⟨9438, true, false, [], []⟩
      ]⟩,
    ⟨[78797], [78797], .contexts []⟩,
    ⟨[78799, 11], [78797], .contexts [
        ⟨9439, true, false, [], [11]⟩,
        ⟨90, false, false, [78797], []⟩,
        ⟨9440, false, false, [], []⟩
      ]⟩,
    ⟨[78801], [78799, 1], .source 39465⟩,
    ⟨[78799, 1], [78801], .contexts [
        ⟨9442, true, false, [], []⟩
      ]⟩,
    ⟨[78799], [78799], .contexts []⟩,
    ⟨[78801, 1], [78799], .contexts [
        ⟨9443, true, false, [], [1]⟩,
        ⟨18, false, false, [78799], []⟩,
        ⟨9444, false, false, [], []⟩
      ]⟩,
    ⟨[78803], [78801, 13], .source 39466⟩,
    ⟨[78801], [78801], .contexts []⟩,
    ⟨[78803, 13], [78801], .contexts [
        ⟨9446, false, false, [], [13]⟩,
        ⟨98, false, false, [78801], []⟩,
        ⟨9447, false, false, [], []⟩
      ]⟩,
    ⟨[78805], [78803, 15], .source 39467⟩,
    ⟨[78803, 15], [78805], .contexts [
        ⟨9449, true, false, [], []⟩
      ]⟩,
    ⟨[78803], [78803], .contexts []⟩,
    ⟨[78805, 15], [78803], .contexts [
        ⟨9450, true, false, [], [15]⟩,
        ⟨3, false, false, [78803], []⟩,
        ⟨9451, false, false, [], []⟩
      ]⟩,
    ⟨[78807], [78805, 1], .source 39468⟩,
    ⟨[78805, 1], [78807], .contexts [
        ⟨9453, true, false, [], []⟩
      ]⟩,
    ⟨[78805], [78805], .contexts []⟩,
    ⟨[78807, 1], [78805], .contexts [
        ⟨9454, true, false, [], [1]⟩,
        ⟨18, false, false, [78805], []⟩,
        ⟨9455, false, false, [], []⟩
      ]⟩,
    ⟨[78809], [78807, 3], .source 39469⟩,
    ⟨[78807], [78807], .contexts []⟩,
    ⟨[78809, 3], [78807], .contexts [
        ⟨9457, false, false, [], [3]⟩,
        ⟨35, false, false, [78807], []⟩,
        ⟨9458, false, false, [], []⟩
      ]⟩,
    ⟨[78811], [78809, 5], .source 39470⟩,
    ⟨[78809, 5], [78811], .contexts [
        ⟨9460, true, false, [], []⟩
      ]⟩,
    ⟨[78809], [78809], .contexts []⟩,
    ⟨[78811, 5], [78809], .contexts [
        ⟨9461, true, false, [], [5]⟩,
        ⟨49, false, false, [78809], []⟩,
        ⟨9462, false, false, [], []⟩
      ]⟩,
    ⟨[78813], [78811, 1], .source 39471⟩,
    ⟨[78811], [78811], .contexts []⟩,
    ⟨[78813, 1], [78811], .contexts [
        ⟨9464, false, false, [], [1]⟩,
        ⟨18, false, false, [78811], []⟩,
        ⟨9465, false, false, [], []⟩
      ]⟩,
    ⟨[78815], [78813, 9], .source 39472⟩,
    ⟨[78813], [78813], .contexts []⟩,
    ⟨[78815, 9], [78813], .contexts [
        ⟨9467, false, false, [], [9]⟩,
        ⟨76, false, false, [78813], []⟩,
        ⟨9468, false, false, [], []⟩
      ]⟩,
    ⟨[78817], [78815, 11], .source 39473⟩,
    ⟨[78815], [78815], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 148. -/
def y322TCContextRaw148 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78817, 11], [78815], .contexts [
        ⟨9470, false, false, [], [11]⟩,
        ⟨90, false, false, [78815], []⟩,
        ⟨9471, false, false, [], []⟩
      ]⟩,
    ⟨[78819], [78817, 1], .source 39474⟩,
    ⟨[78817, 1], [78819], .contexts [
        ⟨9473, true, false, [], []⟩
      ]⟩,
    ⟨[78817], [78817], .contexts []⟩,
    ⟨[78819, 1], [78817], .contexts [
        ⟨9474, true, false, [], [1]⟩,
        ⟨18, false, false, [78817], []⟩,
        ⟨9475, false, false, [], []⟩
      ]⟩,
    ⟨[78821], [78819, 13], .source 39475⟩,
    ⟨[78819, 13], [78821], .contexts [
        ⟨9477, true, false, [], []⟩
      ]⟩,
    ⟨[78819], [78819], .contexts []⟩,
    ⟨[78821, 13], [78819], .contexts [
        ⟨9478, true, false, [], [13]⟩,
        ⟨98, false, false, [78819], []⟩,
        ⟨9479, false, false, [], []⟩
      ]⟩,
    ⟨[78821], [78821], .contexts []⟩,
    ⟨[78815, 9], [78813], .contexts [
        ⟨9469, false, false, [], []⟩
      ]⟩,
    ⟨[78813], [78813], .contexts []⟩,
    ⟨[78813, 1], [78811], .contexts [
        ⟨9466, false, false, [], []⟩
      ]⟩,
    ⟨[78811], [78811], .contexts []⟩,
    ⟨[78811, 5], [78809], .contexts [
        ⟨9463, false, false, [], []⟩
      ]⟩,
    ⟨[78809], [78809], .contexts []⟩,
    ⟨[78819, 1, 11, 9, 1, 5], [78809], .contexts [
        ⟨9476, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9475, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9475, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9472, false, false, [], [9, 1, 5]⟩,
        ⟨9471, false, false, [], [9, 1, 5]⟩,
        ⟨9471, false, false, [], [9, 1, 5]⟩,
        ⟨9482, false, false, [], [1, 5]⟩,
        ⟨9483, false, false, [], [1, 5]⟩,
        ⟨9468, false, false, [], [1, 5]⟩,
        ⟨9468, false, false, [], [1, 5]⟩,
        ⟨9484, false, false, [], [5]⟩,
        ⟨9485, false, false, [], [5]⟩,
        ⟨9465, false, false, [], [5]⟩,
        ⟨9465, false, false, [], [5]⟩,
        ⟨9486, false, false, [], []⟩,
        ⟨9487, false, false, [], []⟩,
        ⟨9462, false, false, [], []⟩,
        ⟨9462, false, false, [], []⟩
      ]⟩,
    ⟨[78809, 3], [78807], .contexts [
        ⟨9459, false, false, [], []⟩
      ]⟩,
    ⟨[78807], [78807], .contexts []⟩,
    ⟨[78803, 13], [78801], .contexts [
        ⟨9448, false, false, [], []⟩
      ]⟩,
    ⟨[78801], [78801], .contexts []⟩,
    ⟨[78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [78799], .contexts [
        ⟨9488, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨9489, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9490, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9458, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9458, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9456, false, false, [], [15, 13, 1]⟩,
        ⟨9455, false, false, [], [15, 13, 1]⟩,
        ⟨9455, false, false, [], [15, 13, 1]⟩,
        ⟨9452, false, false, [], [13, 1]⟩,
        ⟨9451, false, false, [], [13, 1]⟩,
        ⟨9451, false, false, [], [13, 1]⟩,
        ⟨9491, false, false, [], [1]⟩,
        ⟨9492, false, false, [], [1]⟩,
        ⟨9447, false, false, [], [1]⟩,
        ⟨9447, false, false, [], [1]⟩,
        ⟨9445, false, false, [], []⟩,
        ⟨9444, false, false, [], []⟩,
        ⟨9444, false, false, [], []⟩
      ]⟩,
    ⟨[78799, 11], [78797], .contexts [
        ⟨9441, false, false, [], []⟩
      ]⟩,
    ⟨[78797], [78797], .contexts []⟩,
    ⟨[78797, 9], [78795], .contexts [
        ⟨9437, false, false, [], []⟩
      ]⟩,
    ⟨[78795], [78795], .contexts []⟩,
    ⟨[78795, 1], [78793], .contexts [
        ⟨9433, false, false, [], []⟩
      ]⟩,
    ⟨[78793], [78793], .contexts []⟩,
    ⟨[78793, 5], [78791], .contexts [
        ⟨9430, false, false, [], []⟩
      ]⟩,
    ⟨[78791], [78791], .contexts []⟩,
    ⟨[78791, 3], [78789], .contexts [
        ⟨9427, false, false, [], []⟩
      ]⟩,
    ⟨[78789], [78789], .contexts []⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [78789], .contexts [
        ⟨9493, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨9494, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9495, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9440, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9440, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9496, false, false, [], [1, 5, 3]⟩,
        ⟨9497, false, false, [], [1, 5, 3]⟩,
        ⟨9436, false, false, [], [1, 5, 3]⟩,
        ⟨9436, false, false, [], [1, 5, 3]⟩,
        ⟨9498, false, false, [], [5, 3]⟩,
        ⟨9499, false, false, [], [5, 3]⟩,
        ⟨9432, false, false, [], [5, 3]⟩,
        ⟨9432, false, false, [], [5, 3]⟩,
        ⟨9500, false, false, [], [3]⟩,
        ⟨9501, false, false, [], [3]⟩,
        ⟨9429, false, false, [], [3]⟩,
        ⟨9429, false, false, [], [3]⟩,
        ⟨9502, false, false, [], []⟩,
        ⟨9503, false, false, [], []⟩,
        ⟨9426, false, false, [], []⟩,
        ⟨9426, false, false, [], []⟩
      ]⟩,
    ⟨[78787, 15], [78785], .contexts [
        ⟨9420, false, false, [], []⟩
      ]⟩,
    ⟨[78785], [78785], .contexts []⟩,
    ⟨[78785, 13], [78783], .contexts [
        ⟨9416, false, false, [], []⟩
      ]⟩,
    ⟨[78783], [78783], .contexts []⟩,
    ⟨[78783, 1], [78781], .contexts [
        ⟨9412, false, false, [], []⟩
      ]⟩,
    ⟨[78781], [78781], .contexts []⟩,
    ⟨[78781, 11], [78779], .contexts [
        ⟨9408, false, false, [], []⟩
      ]⟩,
    ⟨[78779], [78779], .contexts []⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [78779], .contexts [
        ⟨9504, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨9424, false, false, [], [15, 13, 1, 11]⟩,
        ⟨9423, false, false, [], [15, 13, 1, 11]⟩,
        ⟨9423, false, false, [], [15, 13, 1, 11]⟩,
        ⟨9505, false, false, [], [13, 1, 11]⟩,
        ⟨9506, false, false, [], [13, 1, 11]⟩,
        ⟨9419, false, false, [], [13, 1, 11]⟩,
        ⟨9419, false, false, [], [13, 1, 11]⟩,
        ⟨9507, false, false, [], [1, 11]⟩,
        ⟨9508, false, false, [], [1, 11]⟩,
        ⟨9415, false, false, [], [1, 11]⟩,
        ⟨9415, false, false, [], [1, 11]⟩,
        ⟨9509, false, false, [], [11]⟩,
        ⟨9510, false, false, [], [11]⟩,
        ⟨9411, false, false, [], [11]⟩,
        ⟨9411, false, false, [], [11]⟩,
        ⟨9511, false, false, [], []⟩,
        ⟨9512, false, false, [], []⟩,
        ⟨9407, false, false, [], []⟩,
        ⟨9407, false, false, [], []⟩
      ]⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [78771], .contexts [
        ⟨9513, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9403, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [78777], [1, 5, 3]⟩,
        ⟨9404, false, false, [], [1, 5, 3]⟩,
        ⟨9404, false, false, [], [1, 5, 3]⟩,
        ⟨9404, false, false, [], [1, 5, 3]⟩,
        ⟨9401, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [78775], [5, 3]⟩,
        ⟨9402, false, false, [], [5, 3]⟩,
        ⟨9402, false, false, [], [5, 3]⟩,
        ⟨9402, false, false, [], [5, 3]⟩,
        ⟨9399, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [78773], [3]⟩,
        ⟨9400, false, false, [], [3]⟩,
        ⟨9400, false, false, [], [3]⟩,
        ⟨9400, false, false, [], [3]⟩,
        ⟨9397, false, false, [], [3]⟩,
        ⟨35, false, false, [78771], []⟩,
        ⟨9398, false, false, [], []⟩,
        ⟨9398, false, false, [], []⟩,
        ⟨9398, false, false, [], []⟩
      ]⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [78763], .contexts [
        ⟨9514, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9395, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [78769], [15, 13, 1]⟩,
        ⟨9396, false, false, [], [15, 13, 1]⟩,
        ⟨9396, false, false, [], [15, 13, 1]⟩,
        ⟨9396, false, false, [], [15, 13, 1]⟩,
        ⟨9393, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [78767], [13, 1]⟩,
        ⟨9394, false, false, [], [13, 1]⟩,
        ⟨9394, false, false, [], [13, 1]⟩,
        ⟨9394, false, false, [], [13, 1]⟩,
        ⟨9391, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [78765], [1]⟩,
        ⟨9392, false, false, [], [1]⟩,
        ⟨9392, false, false, [], [1]⟩,
        ⟨9392, false, false, [], [1]⟩,
        ⟨9389, false, false, [], [1]⟩,
        ⟨18, false, false, [78763], []⟩,
        ⟨9390, false, false, [], []⟩,
        ⟨9390, false, false, [], []⟩,
        ⟨9390, false, false, [], []⟩
      ]⟩,
    ⟨[78755], [78755], .contexts []⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [78755], .contexts [
        ⟨9515, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9387, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [78761], [9, 1, 5]⟩,
        ⟨9388, false, false, [], [9, 1, 5]⟩,
        ⟨9388, false, false, [], [9, 1, 5]⟩,
        ⟨9388, false, false, [], [9, 1, 5]⟩,
        ⟨9385, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [78759], [1, 5]⟩,
        ⟨9386, false, false, [], [1, 5]⟩,
        ⟨9386, false, false, [], [1, 5]⟩,
        ⟨9386, false, false, [], [1, 5]⟩,
        ⟨9383, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [78757], [5]⟩,
        ⟨9384, false, false, [], [5]⟩,
        ⟨9384, false, false, [], [5]⟩,
        ⟨9384, false, false, [], [5]⟩,
        ⟨9381, false, false, [], [5]⟩,
        ⟨49, false, false, [78755], []⟩,
        ⟨9382, false, false, [], []⟩,
        ⟨9516, false, false, [], []⟩,
        ⟨9382, false, false, [], []⟩,
        ⟨9382, false, false, [], []⟩
      ]⟩,
    ⟨[78753], [78753], .contexts []⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [78747], .contexts [
        ⟨9517, false, false, [], [3, 1, 15, 13]⟩,
        ⟨9379, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [78753], [1, 15, 13]⟩,
        ⟨9380, false, false, [], [1, 15, 13]⟩,
        ⟨9518, false, false, [], [1, 15, 13]⟩,
        ⟨9380, false, false, [], [1, 15, 13]⟩,
        ⟨9380, false, false, [], [1, 15, 13]⟩,
        ⟨9376, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [78751], [15, 13]⟩,
        ⟨9377, false, false, [], [15, 13]⟩,
        ⟨9377, false, false, [], [15, 13]⟩,
        ⟨9377, false, false, [], [15, 13]⟩,
        ⟨9373, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [78749], [13]⟩,
        ⟨9374, false, false, [], [13]⟩,
        ⟨9374, false, false, [], [13]⟩,
        ⟨9374, false, false, [], [13]⟩,
        ⟨9371, true, false, [], [13]⟩,
        ⟨98, false, false, [78747], []⟩,
        ⟨9363, false, false, [], []⟩,
        ⟨9362, false, false, [], []⟩,
        ⟨9363, false, false, [], []⟩,
        ⟨9363, false, false, [], []⟩
      ]⟩,
    ⟨[2245], [283, 1755], .source 1187⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5
    ], [2245, 78545], .contexts [
        ⟨9519, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨9369, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9366, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9367, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9367, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9360, true, false, [283], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [283, 78745], [9, 1, 5]⟩,
        ⟨9346, false, false, [283], [9, 1, 5]⟩,
        ⟨9352, false, false, [], [9, 1, 5]⟩,
        ⟨9353, false, false, [], [9, 1, 5]⟩,
        ⟨9354, false, false, [], [9, 1, 5]⟩,
        ⟨9343, false, false, [283], [1, 5]⟩,
        ⟨9349, false, false, [], [1, 5]⟩,
        ⟨9350, false, false, [], [1, 5]⟩,
        ⟨9351, false, false, [], [1, 5]⟩,
        ⟨1213, false, false, [283], [5]⟩,
        ⟨9347, false, false, [], [5]⟩,
        ⟨9348, false, false, [], [5]⟩,
        ⟨8342, false, false, [283], []⟩,
        ⟨9520, true, false, [], [78545]⟩
      ]⟩,
    ⟨[2247], [2245, 1423], .source 1188⟩,
    ⟨[2249], [2247, 1421], .source 1189⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [2249, 78127], .contexts [
        ⟨9521, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨8334, false, false, [2245], [1, 15, 13, 1]⟩,
        ⟨448, false, false, [2245], [15, 13, 1]⟩,
        ⟨6682, false, false, [2245], [13, 1]⟩,
        ⟨9522, true, false, [], [78257, 13, 1]⟩,
        ⟨6785, false, false, [2247], [1]⟩,
        ⟨6789, false, false, [2247], []⟩,
        ⟨9523, true, false, [], [78127]⟩
      ]⟩,
    ⟨[2251], [2249, 1219], .source 1190⟩,
    ⟨[2253], [2251, 1209], .source 1191⟩,
    ⟨[2255], [2253, 841], .source 1192⟩,
    ⟨[2257], [2255, 1213], .source 1193⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [2257, 77705], .contexts [
        ⟨9524, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨6265, false, false, [2249], [9, 1, 5, 3]⟩,
        ⟨9525, true, false, [], [77703, 9, 1, 5, 3]⟩,
        ⟨3887, false, false, [2251], [1, 5, 3]⟩,
        ⟨5512, false, false, [2251], [5, 3]⟩,
        ⟨9526, true, false, [], [77705, 5, 3]⟩,
        ⟨4093, false, false, [2253], [3]⟩,
        ⟨9527, true, false, [], [77705, 3]⟩,
        ⟨5517, false, false, [2255], []⟩,
        ⟨9528, true, false, [], [77705]⟩
      ]⟩,
    ⟨[2259], [2257, 1209], .source 1194⟩,
    ⟨[2261], [2259, 831], .source 1195⟩,
    ⟨[2263], [2261, 1217], .source 1196⟩,
    ⟨[2265], [2263, 315], .source 1197⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [2265, 77985], .contexts [
        ⟨9529, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨5512, false, false, [2257], [15, 13, 1, 11]⟩,
        ⟨9530, true, false, [], [77705, 15, 13, 1, 11]⟩,
        ⟨4080, false, false, [2259], [13, 1, 11]⟩,
        ⟨9531, true, false, [], [77705, 13, 1, 11]⟩,
        ⟨5507, false, false, [2261], [1, 11]⟩,
        ⟨9532, true, false, [], [77123, 1, 11]⟩,
        ⟨429, false, false, [2263], [11]⟩,
        ⟨1942, false, false, [2263], [11]⟩,
        ⟨9533, true, false, [], [77119, 11]⟩,
        ⟨5463, false, false, [2265], []⟩
      ]⟩,
    ⟨[2267], [2265, 245], .source 1198⟩]

/-- Exact literal claimed equations and contextual derivations, block 149. -/
def y322TCContextRaw149 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2269], [2267, 1201], .source 1199⟩,
    ⟨[2271], [2269, 843], .source 1200⟩,
    ⟨[2273], [2271, 837], .source 1201⟩,
    ⟨[2275], [2273, 1203], .source 1202⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [2275, 77985], .contexts [
        ⟨9534, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨5476, false, false, [2265], [1, 5, 3, 1]⟩,
        ⟨9535, true, false, [], [77985, 1, 5, 3, 1]⟩,
        ⟨5470, false, false, [2267], [5, 3, 1]⟩,
        ⟨9536, true, false, [], [77711, 5, 3, 1]⟩,
        ⟨4049, false, false, [2269], [3, 1]⟩,
        ⟨9537, true, false, [], [77711, 3, 1]⟩,
        ⟨4040, false, false, [2271], [1]⟩,
        ⟨9538, true, false, [], [77711, 1]⟩,
        ⟨5472, false, false, [2273], []⟩,
        ⟨9539, true, false, [], [77985]⟩
      ]⟩,
    ⟨[2277], [2275, 505], .source 1203⟩,
    ⟨[2279], [2277, 257], .source 1204⟩,
    ⟨[2281], [2279, 507], .source 1205⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [2281, 77471], .contexts [
        ⟨9540, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨5481, false, false, [2275], [13, 1, 11, 9]⟩,
        ⟨9541, true, false, [], [77347, 13, 1, 11, 9]⟩,
        ⟨1344, false, false, [2277], [1, 11, 9]⟩,
        ⟨1566, false, false, [2277], [11, 9]⟩,
        ⟨9542, true, false, [], [77349, 11, 9]⟩,
        ⟨2675, false, false, [2279], [9]⟩,
        ⟨2712, false, false, [2279], []⟩,
        ⟨9543, true, false, [], [77471]⟩
      ]⟩,
    ⟨[2283], [2281, 439], .source 1206⟩,
    ⟨[2285], [2283, 455], .source 1207⟩,
    ⟨[2287], [2285, 449], .source 1208⟩,
    ⟨[2289], [2287, 451], .source 1209⟩,
    ⟨[2291], [2289, 439], .source 1210⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [2291, 77471], .contexts [
        ⟨9544, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨2286, false, false, [2281], [5, 3, 1, 15]⟩,
        ⟨2503, false, false, [2281], [5, 3, 1, 15]⟩,
        ⟨9545, true, false, [], [77467, 5, 3, 1, 15]⟩,
        ⟨2506, false, false, [2283], [3, 1, 15]⟩,
        ⟨9546, true, false, [], [77467, 3, 1, 15]⟩,
        ⟨2492, false, false, [2285], [1, 15]⟩,
        ⟨9547, true, false, [], [77467, 1, 15]⟩,
        ⟨2499, false, false, [2287], [15]⟩,
        ⟨9548, true, false, [], [77471, 15]⟩,
        ⟨2470, false, false, [2289], []⟩,
        ⟨9549, true, false, [], [77471]⟩
      ]⟩,
    ⟨[2293], [2291, 655], .source 1211⟩,
    ⟨[2295], [2293, 663], .source 1212⟩,
    ⟨[2297], [2295, 677], .source 1213⟩,
    ⟨[2299], [2297, 267], .source 1214⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [2299, 77341], .contexts [
        ⟨9550, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨3294, false, false, [2291], [1, 11, 9, 1]⟩,
        ⟨9551, true, false, [], [77603, 1, 11, 9, 1]⟩,
        ⟨3151, false, false, [2293], [11, 9, 1]⟩,
        ⟨3306, false, false, [2293], [9, 1]⟩,
        ⟨9552, true, false, [], [77601, 9, 1]⟩,
        ⟨3329, false, false, [2295], [1]⟩,
        ⟨9553, true, false, [], [77337, 1]⟩,
        ⟨1701, false, false, [2297], []⟩,
        ⟨9554, true, false, [], [77341]⟩
      ]⟩,
    ⟨[2301], [2299, 261], .source 1215⟩,
    ⟨[2303], [2301, 491], .source 1216⟩,
    ⟨[2305], [2303, 261], .source 1217⟩,
    ⟨[2307], [2305, 1277], .source 1218⟩,
    ⟨[2309], [2307, 693], .source 1219⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [2309, 77591], .contexts [
        ⟨9555, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨1674, false, false, [2299], [3, 1, 15, 13]⟩,
        ⟨9556, true, false, [], [77341, 3, 1, 15, 13]⟩,
        ⟨2623, false, false, [2301], [1, 15, 13]⟩,
        ⟨9557, true, false, [], [77341, 1, 15, 13]⟩,
        ⟨1330, false, false, [2303], [15, 13]⟩,
        ⟨2626, false, false, [2303], [15, 13]⟩,
        ⟨9558, true, false, [], [77337, 15, 13]⟩,
        ⟨5673, false, false, [2305], [13]⟩,
        ⟨9559, true, false, [], [77993, 13]⟩,
        ⟨5686, false, false, [2307], []⟩,
        ⟨9560, true, false, [], [77591]⟩
      ]⟩,
    ⟨[2311], [2309, 697], .source 1220⟩,
    ⟨[2313], [2311, 1429], .source 1221⟩,
    ⟨[2315], [2313, 1937], .source 1222⟩,
    ⟨[2317], [2315, 1453], .source 1223⟩,
    ⟨[
      78819, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5
    ], [2317, 78541], .contexts [
        ⟨9561, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨3132, false, false, [2309], [11, 9, 1, 5]⟩,
        ⟨3391, false, false, [2309], [11, 9, 1, 5]⟩,
        ⟨9562, true, false, [], [77587, 11, 9, 1, 5]⟩,
        ⟨6654, false, false, [2311], [9, 1, 5]⟩,
        ⟨9563, true, false, [], [78257, 9, 1, 5]⟩,
        ⟨8208, false, false, [2313], [1, 5]⟩,
        ⟨8214, false, false, [2313], [5]⟩,
        ⟨9564, true, false, [], [78541, 5]⟩,
        ⟨8210, true, false, [2315], [5]⟩,
        ⟨1805, false, false, [2315, 78257], []⟩,
        ⟨1806, false, false, [2315, 78257], []⟩,
        ⟨6676, false, false, [2315], [9]⟩,
        ⟨6790, false, false, [2315], [9]⟩,
        ⟨6791, false, false, [2315], [9]⟩,
        ⟨6791, false, false, [2315], [9]⟩,
        ⟨8208, false, false, [2315, 1453], []⟩,
        ⟨8213, false, false, [2315, 1453], []⟩,
        ⟨24, true, false, [2315], [1453, 78541]⟩,
        ⟨9565, true, false, [], [78541]⟩
      ]⟩,
    ⟨[2319], [2317, 1903], .source 1224⟩,
    ⟨[2319, 78517], [2319, 78517], .contexts []⟩,
    ⟨[2319, 78517], [2319, 78517], .contexts []⟩,
    ⟨[78821, 15], [78821, 15], .contexts []⟩,
    ⟨[78821, 15], [2319, 78517], .contexts [
        ⟨9570, false, false, [], []⟩,
        ⟨9481, true, false, [], [15]⟩,
        ⟨9481, true, false, [], [15]⟩,
        ⟨9478, true, false, [], [15]⟩,
        ⟨4009, false, false, [78819], []⟩,
        ⟨4017, false, false, [78819], []⟩,
        ⟨9566, false, false, [], [3, 1]⟩,
        ⟨8221, false, false, [2317], [1]⟩,
        ⟨9567, true, false, [], [78519, 1]⟩,
        ⟨7856, false, false, [2319], []⟩,
        ⟨9568, false, false, [], []⟩,
        ⟨9569, false, false, [], []⟩,
        ⟨8134, false, false, [2319], []⟩,
        ⟨24, true, false, [], [2319, 78517]⟩
      ]⟩,
    ⟨[2321], [2318], .source 1225⟩,
    ⟨[78517, 15], [2321, 78821], .contexts [
        ⟨9571, true, false, [2318], [15]⟩,
        ⟨3, false, false, [2318, 78821], []⟩,
        ⟨9572, true, false, [], [78821]⟩
      ]⟩,
    ⟨[78821, 15], [2319, 78517], .contexts [
        ⟨9570, false, false, [], []⟩,
        ⟨9571, false, false, [], []⟩,
        ⟨9568, false, false, [], []⟩,
        ⟨9569, false, false, [], []⟩,
        ⟨9569, false, false, [], []⟩
      ]⟩,
    ⟨[2323], [2319, 1885], .source 1226⟩,
    ⟨[78821], [78821], .contexts []⟩,
    ⟨[78737, 1], [78737, 1], .contexts []⟩,
    ⟨[78821], [78821], .contexts []⟩,
    ⟨[2325], [2322], .source 1227⟩,
    ⟨[2322], [2322], .contexts []⟩,
    ⟨[78737, 1], [2325, 78821], .contexts [
        ⟨9577, false, false, [], []⟩,
        ⟨9575, false, false, [2322], [78737, 1]⟩,
        ⟨9340, false, false, [2322, 2319], [78737, 1]⟩,
        ⟨3, true, false, [2322, 2319, 1886, 78737], [1]⟩,
        ⟨9339, false, false, [2322, 2319, 1886], [15, 1]⟩,
        ⟨7854, true, false, [2322, 2319], [15, 1]⟩,
        ⟨9574, true, false, [2322], [1, 15, 1]⟩,
        ⟨911, false, false, [2322, 78821], []⟩,
        ⟨9576, false, false, [2322], []⟩,
        ⟨9578, false, false, [2322], []⟩,
        ⟨9580, true, false, [], [78821]⟩,
        ⟨9580, true, false, [], [78821]⟩,
        ⟨9579, true, false, [], [78821]⟩
      ]⟩,
    ⟨[2323], [2324], .contexts [
        ⟨9579, true, true, [], []⟩
      ]⟩,
    ⟨[2327], [2319, 1925], .source 1228⟩,
    ⟨[2329], [2327, 2321], .source 1229⟩,
    ⟨[2331], [2328], .source 1230⟩,
    ⟨[2328], [2328], .contexts []⟩,
    ⟨[2333], [2319, 1919], .source 1231⟩,
    ⟨[2335], [2333, 2321], .source 1232⟩,
    ⟨[78821, 11], [78821, 11], .contexts []⟩,
    ⟨[2337], [2334], .source 1233⟩,
    ⟨[2334], [2334], .contexts []⟩,
    ⟨[78737, 1], [2325, 78821], .contexts [
        ⟨9581, false, false, [], []⟩
      ]⟩,
    ⟨[2325, 78821], [2325, 78821], .contexts []⟩,
    ⟨[2325, 78821], [2325, 78821], .contexts []⟩,
    ⟨[2325, 78821, 13], [2325, 78819], .contexts [
        ⟨9480, false, false, [2325], []⟩
      ]⟩,
    ⟨[2339], [1077, 2325], .source 1234⟩,
    ⟨[78817, 13], [2324, 2339, 78821], .contexts [
        ⟨9476, true, false, [], [13]⟩,
        ⟨9595, true, false, [2324], [1, 13]⟩,
        ⟨9594, true, false, [2324], [13, 1, 13]⟩,
        ⟨9594, true, false, [2324], [13, 1, 13]⟩,
        ⟨9593, true, false, [2324], [13, 1, 13]⟩,
        ⟨9592, true, false, [2324], [13, 1, 13]⟩,
        ⟨9577, true, false, [2324], [13, 1, 13]⟩,
        ⟨1587, false, false, [2324, 78737], []⟩,
        ⟨190, false, false, [2324, 78737], []⟩,
        ⟨9331, false, false, [2324], [1]⟩,
        ⟨9331, false, false, [2324], [1]⟩,
        ⟨9327, true, false, [2324], [13, 1]⟩,
        ⟨315, false, false, [2324, 77137], [1]⟩,
        ⟨316, false, false, [2324, 77137], [1]⟩,
        ⟨4944, false, false, [2324], [9, 1]⟩,
        ⟨9323, false, false, [2324, 1077], [1]⟩,
        ⟨9329, false, false, [2324], [1]⟩,
        ⟨9330, false, false, [2324], [1]⟩,
        ⟨9328, false, false, [2324, 1077], [1]⟩,
        ⟨24, true, false, [2324], [1077, 78737, 1]⟩,
        ⟨9329, false, false, [2324], [1]⟩,
        ⟨9330, false, false, [2324], [1]⟩,
        ⟨9330, false, false, [2324], [1]⟩,
        ⟨9581, false, false, [2324, 1077], []⟩,
        ⟨9596, true, false, [2324], [78821]⟩
      ]⟩,
    ⟨[2341], [2323, 2339], .source 1235⟩,
    ⟨[2343], [2340], .source 1236⟩]

/-- Exact literal claimed equations and contextual derivations, block 150. -/
def y322TCContextRaw150 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78821, 13], [78819], .contexts [
        ⟨9480, false, false, [], []⟩
      ]⟩,
    ⟨[2343, 78817], [2343, 78817], .contexts []⟩,
    ⟨[78819], [2343, 78817], .contexts [
        ⟨9479, true, false, [], []⟩,
        ⟨9479, true, false, [], []⟩,
        ⟨9600, true, false, [], []⟩,
        ⟨9598, false, false, [2340], [78821, 13]⟩,
        ⟨9582, false, false, [2340], [2339, 78821, 13]⟩,
        ⟨9578, true, false, [2340, 2324, 2339], [13]⟩,
        ⟨9597, true, false, [2340], [13]⟩,
        ⟨98, false, false, [2340, 78817], []⟩,
        ⟨9599, true, false, [], [78817]⟩,
        ⟨9601, false, false, [], []⟩
      ]⟩,
    ⟨[2337, 78821], [2337, 78821], .contexts []⟩,
    ⟨[78821, 11], [2337, 78821], .contexts [
        ⟨9589, false, false, [], []⟩,
        ⟨9589, false, false, [], []⟩,
        ⟨9588, false, false, [2334], [78821, 11]⟩,
        ⟨9573, true, false, [2334, 2333], [11]⟩,
        ⟨9587, false, false, [2334], [78517, 15, 11]⟩,
        ⟨8148, true, false, [2334, 2319], [15, 11]⟩,
        ⟨9574, true, false, [2334], [11, 15, 11]⟩,
        ⟨4051, false, false, [2334, 78821], []⟩,
        ⟨9576, false, false, [2334], []⟩,
        ⟨9578, false, false, [2334], []⟩,
        ⟨9591, true, false, [], [78821]⟩,
        ⟨9591, true, false, [], [78821]⟩,
        ⟨9590, true, false, [], [78821]⟩,
        ⟨9603, false, false, [], []⟩,
        ⟨9603, false, false, [], []⟩
      ]⟩,
    ⟨[2351], [2337, 2343], .source 1240⟩,
    ⟨[2351, 78815], [2351, 78815], .contexts []⟩,
    ⟨[2353], [2350], .source 1241⟩,
    ⟨[2350], [2350], .contexts []⟩,
    ⟨[2343, 78817], [2351, 78815], .contexts [
        ⟨9601, true, false, [], []⟩,
        ⟨9601, true, false, [], []⟩,
        ⟨9602, true, false, [], []⟩,
        ⟨9600, true, false, [], []⟩,
        ⟨9607, false, false, [2352], [78821, 13]⟩,
        ⟨9608, false, false, [2352], [78821, 13]⟩,
        ⟨9608, false, false, [2352], [78821, 13]⟩,
        ⟨9578, true, false, [2352, 2350], [13]⟩,
        ⟨9576, true, false, [2352, 2350], [13]⟩,
        ⟨1836, true, false, [2352, 2350, 78821], [13]⟩,
        ⟨9604, false, false, [2352, 2350], [13, 11, 13, 13]⟩,
        ⟨9480, false, false, [2352, 2350, 2337], [11, 13, 13]⟩,
        ⟨9602, false, false, [2352, 2350, 2337], [11, 13, 13]⟩,
        ⟨9605, true, false, [2352, 2350], [78817, 11, 13, 13]⟩,
        ⟨9472, false, false, [2352], [13, 13]⟩,
        ⟨9606, false, false, [2352, 2350], [13, 13]⟩,
        ⟨98, false, false, [2352, 78815], []⟩,
        ⟨9607, false, true, [], [78815]⟩
      ]⟩,
    ⟨[2355], [2341, 2351], .source 1242⟩,
    ⟨[78817], [2355, 78815], .contexts [
        ⟨9609, false, false, [2342], []⟩,
        ⟨9606, false, false, [2342], []⟩,
        ⟨9599, false, true, [], [2351, 78815]⟩,
        ⟨9610, true, false, [], [78815]⟩
      ]⟩,
    ⟨[2357], [2343, 2355], .source 1243⟩,
    ⟨[78819], [2357, 78815], .contexts [
        ⟨9602, false, false, [], []⟩,
        ⟨9611, false, false, [2343], []⟩,
        ⟨9612, true, false, [], [78815]⟩
      ]⟩,
    ⟨[78819], [2357, 78815], .contexts [
        ⟨9613, false, false, [], []⟩
      ]⟩,
    ⟨[2359], [2354], .source 1244⟩,
    ⟨[2361], [2359, 2357], .source 1245⟩,
    ⟨[2361, 78815], [2361, 78815], .contexts []⟩,
    ⟨[2361, 78811, 9], [78815, 1, 9, 1, 9], .contexts [
        ⟨9466, true, false, [2361], [9]⟩,
        ⟨9469, true, false, [2361], [1, 9]⟩,
        ⟨9617, true, false, [], [9, 1, 9]⟩,
        ⟨9617, true, false, [], [9, 1, 9]⟩,
        ⟨9616, false, false, [], [78815, 9, 1, 9]⟩,
        ⟨9615, false, false, [], [2357, 78815, 9, 1, 9]⟩,
        ⟨9614, true, false, [2354], [9, 1, 9]⟩,
        ⟨9474, true, false, [2354], [9, 1, 9]⟩,
        ⟨9611, false, false, [2354], [1, 9, 1, 9]⟩
      ]⟩,
    ⟨[78811, 9], [78811, 9], .contexts []⟩,
    ⟨[78811], [78811], .contexts []⟩,
    ⟨[2367], [2360], .source 1248⟩,
    ⟨[2360], [2360], .contexts []⟩,
    ⟨[2367], [2360], .contexts [
        ⟨9621, false, false, [], []⟩,
        ⟨9622, false, false, [], []⟩,
        ⟨9622, false, false, [], []⟩
      ]⟩,
    ⟨[2367, 78811], [2367, 78811], .contexts []⟩,
    ⟨[78811, 9, 5], [2367, 78809], .contexts [
        ⟨9619, false, false, [], [5]⟩,
        ⟨9619, false, false, [], [5]⟩,
        ⟨9618, false, false, [2360], [5]⟩,
        ⟨1022, false, false, [2360, 78815], [5]⟩,
        ⟨787, false, false, [2360, 78815], [5]⟩,
        ⟨9482, false, false, [2360], [1, 5]⟩,
        ⟨9483, false, false, [2360], [1, 5]⟩,
        ⟨9468, false, false, [2360], [1, 5]⟩,
        ⟨9468, false, false, [2360], [1, 5]⟩,
        ⟨9484, false, false, [2360], [5]⟩,
        ⟨9485, false, false, [2360], [5]⟩,
        ⟨9465, false, false, [2360], [5]⟩,
        ⟨9465, false, false, [2360], [5]⟩,
        ⟨9620, false, false, [2360], [5]⟩,
        ⟨9623, true, false, [], [78811, 5]⟩,
        ⟨9624, false, false, [], [5]⟩,
        ⟨9624, false, false, [], [5]⟩,
        ⟨9463, false, false, [2367], []⟩
      ]⟩,
    ⟨[78809, 9], [78809, 9], .contexts []⟩,
    ⟨[78809], [78809], .contexts []⟩,
    ⟨[2366], [2366], .contexts []⟩,
    ⟨[78809, 9], [2361, 78809], .contexts [
        ⟨9626, false, false, [], []⟩,
        ⟨9625, true, false, [2366], [9]⟩,
        ⟨1034, false, false, [2366, 78811], []⟩,
        ⟨50, false, false, [2366, 78811], []⟩,
        ⟨9486, false, false, [2366], []⟩,
        ⟨9487, false, false, [2366], []⟩,
        ⟨9462, false, false, [2366], []⟩,
        ⟨9462, false, false, [2366], []⟩,
        ⟨9627, false, false, [2366], []⟩,
        ⟨9628, true, false, [], [78809]⟩,
        ⟨9628, true, false, [], [78809]⟩,
        ⟨9621, false, true, [], [78809]⟩
      ]⟩,
    ⟨[2361, 78809], [2361, 78809], .contexts []⟩,
    ⟨[78809, 3], [78807], .contexts [
        ⟨9489, false, false, [], []⟩,
        ⟨9490, false, false, [], []⟩,
        ⟨9458, false, false, [], []⟩,
        ⟨9458, false, false, [], []⟩
      ]⟩,
    ⟨[78809, 2], [78809, 3], .contexts [
        ⟨36, false, false, [78809], []⟩
      ]⟩,
    ⟨[78807], [78807], .contexts []⟩,
    ⟨[78825], [78717, 9], .source 39477⟩,
    ⟨[78717, 9], [78825], .contexts [
        ⟨9634, true, false, [], []⟩
      ]⟩,
    ⟨[78825, 9], [78717], .contexts [
        ⟨9635, true, false, [], [9]⟩,
        ⟨76, false, false, [78717], []⟩,
        ⟨9103, false, false, [], []⟩
      ]⟩,
    ⟨[78825], [78825], .contexts []⟩,
    ⟨[78825], [78825], .contexts []⟩,
    ⟨[78717, 9], [78825], .contexts [
        ⟨9635, false, false, [], []⟩,
        ⟨9637, false, false, [], []⟩,
        ⟨9638, false, false, [], []⟩,
        ⟨9638, false, false, [], []⟩
      ]⟩,
    ⟨[78825, 5], [78825, 5], .contexts []⟩,
    ⟨[77143], [77143], .contexts [
        ⟨8440, false, false, [], []⟩
      ]⟩,
    ⟨[77143], [77143], .contexts [
        ⟨1118, true, false, [], [77143]⟩
      ]⟩,
    ⟨[78825, 5], [77143], .contexts [
        ⟨9640, false, false, [], []⟩,
        ⟨9639, true, false, [], [5]⟩,
        ⟨1805, false, false, [78717], []⟩,
        ⟨1806, false, false, [78717], []⟩,
        ⟨9105, false, false, [], [9]⟩,
        ⟨9106, false, false, [], [9]⟩,
        ⟨710, false, false, [], [9]⟩,
        ⟨463, false, false, [], [9]⟩,
        ⟨463, false, false, [], [9]⟩,
        ⟨9192, false, false, [], []⟩,
        ⟨708, false, false, [], []⟩,
        ⟨467, false, false, [], []⟩,
        ⟨467, false, false, [], []⟩,
        ⟨9641, false, false, [], []⟩,
        ⟨9642, false, false, [], []⟩
      ]⟩,
    ⟨[77143, 5], [78825], .contexts [
        ⟨9643, true, false, [], [5]⟩,
        ⟨49, false, false, [78825], []⟩,
        ⟨9638, false, false, [], []⟩
      ]⟩,
    ⟨[78717, 13], [2191, 77575], .contexts [
        ⟨9139, false, false, [2192], [78717, 13]⟩,
        ⟨1836, true, false, [2192, 2190, 78717], [13]⟩,
        ⟨9129, false, false, [2192, 2190], [13, 11, 13, 13]⟩,
        ⟨9130, false, false, [2192, 2190], [11, 13, 13]⟩,
        ⟨9131, false, false, [2192, 2190], [11, 13, 13]⟩,
        ⟨9132, false, false, [2192, 2190], [11, 13, 13]⟩,
        ⟨9134, false, false, [2192, 2190], [11, 13, 13]⟩,
        ⟨3106, false, false, [2192], [13, 13]⟩,
        ⟨9135, false, false, [2192, 2190], [13, 13]⟩,
        ⟨9136, false, false, [2192, 2190], [13, 13]⟩,
        ⟨98, false, false, [2192, 77575], []⟩,
        ⟨9140, true, false, [], [77575]⟩
      ]⟩,
    ⟨[2191, 77573], [2191, 77573], .contexts []⟩,
    ⟨[2191, 77573], [2191, 77573], .contexts []⟩,
    ⟨[2191, 77573], [2191, 77573], .contexts [
        ⟨3540, false, false, [2191], []⟩
      ]⟩,
    ⟨[2191], [2191], .contexts [
        ⟨24, false, false, [], [2191]⟩
      ]⟩,
    ⟨[2191, 77573], [2191, 77573], .contexts [
        ⟨9649, true, false, [], [77573]⟩
      ]⟩,
    ⟨[78825, 13], [2191, 77573], .contexts [
        ⟨9639, true, false, [], [13]⟩,
        ⟨315, false, false, [78717], []⟩,
        ⟨316, false, false, [78717], []⟩,
        ⟨9645, false, false, [], [9]⟩,
        ⟨9135, false, false, [], [9]⟩,
        ⟨9136, false, false, [], [9]⟩,
        ⟨9136, false, false, [], [9]⟩,
        ⟨3102, false, false, [2191], []⟩,
        ⟨9646, false, false, [], []⟩,
        ⟨9647, false, false, [], []⟩,
        ⟨9648, false, false, [], []⟩,
        ⟨9650, false, false, [], []⟩
      ]⟩,
    ⟨[2187, 77685], [2187, 77685], .contexts []⟩,
    ⟨[2187, 77685], [2187, 77685], .contexts []⟩,
    ⟨[78825, 15], [78825, 15], .contexts []⟩,
    ⟨[78825, 15], [2187, 77685], .contexts [
        ⟨9654, false, false, [], []⟩,
        ⟨9639, true, false, [], [15]⟩,
        ⟨323, false, false, [78717], []⟩,
        ⟨324, false, false, [78717], []⟩,
        ⟨9159, false, false, [], [9]⟩,
        ⟨3859, false, false, [2187], []⟩,
        ⟨9652, false, false, [], []⟩,
        ⟨9653, false, false, [], []⟩,
        ⟨5599, false, false, [2187], []⟩,
        ⟨9124, true, false, [], [77685]⟩
      ]⟩,
    ⟨[78827], [78825, 1], .source 39478⟩,
    ⟨[78825, 1], [78827], .contexts [
        ⟨9656, true, false, [], []⟩
      ]⟩,
    ⟨[78825, 1], [78827], .contexts [
        ⟨9657, false, false, [], []⟩
      ]⟩,
    ⟨[78827], [78827], .contexts []⟩,
    ⟨[78827], [78827], .contexts []⟩,
    ⟨[78825, 1], [78827], .contexts [
        ⟨9658, false, false, [], []⟩,
        ⟨9659, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩
      ]⟩,
    ⟨[78827, 9], [78827, 9], .contexts []⟩,
    ⟨[2325, 78821], [2325, 78821], .contexts [
        ⟨9578, false, false, [2325], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 151. -/
def y322TCContextRaw151 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78827, 9], [2325, 78821], .contexts [
        ⟨9662, false, false, [], []⟩,
        ⟨9661, true, false, [], [9]⟩,
        ⟨786, false, false, [78825], []⟩,
        ⟨788, false, false, [78825], []⟩,
        ⟨9636, false, false, [], [1, 9, 1]⟩,
        ⟨9102, false, false, [], [1, 9, 1]⟩,
        ⟨9103, false, false, [], [1, 9, 1]⟩,
        ⟨9103, false, false, [], [1, 9, 1]⟩,
        ⟨9147, false, false, [], [9, 1]⟩,
        ⟨715, false, false, [], [9, 1]⟩,
        ⟨457, false, false, [], [9, 1]⟩,
        ⟨457, false, false, [], [9, 1]⟩,
        ⟨9324, false, false, [], [1]⟩,
        ⟨9325, false, false, [], [1]⟩,
        ⟨9326, false, false, [], [1]⟩,
        ⟨9326, false, false, [], [1]⟩,
        ⟨9592, false, false, [], []⟩,
        ⟨9593, false, false, [], []⟩,
        ⟨9594, false, false, [], []⟩,
        ⟨9594, false, false, [], []⟩,
        ⟨9663, false, false, [], []⟩
      ]⟩,
    ⟨[2325], [2325], .contexts []⟩,
    ⟨[2325], [2325], .contexts []⟩,
    ⟨[2325, 78821], [2325, 78821], .contexts [
        ⟨9666, true, false, [], [78821]⟩,
        ⟨9665, true, false, [], [78821]⟩,
        ⟨24, true, false, [], [2325, 78821]⟩
      ]⟩,
    ⟨[78827, 9], [2325, 78821], .contexts [
        ⟨9664, false, false, [], []⟩,
        ⟨9667, false, false, [], []⟩
      ]⟩,
    ⟨[2187, 77683], [2187, 77683], .contexts []⟩,
    ⟨[2187, 77683], [2187, 77683], .contexts []⟩,
    ⟨[2187, 77683], [2187, 77683], .contexts [
        ⟨7593, false, false, [2187], []⟩
      ]⟩,
    ⟨[2187, 77683], [2187, 77683], .contexts [
        ⟨9124, true, false, [], [77683]⟩
      ]⟩,
    ⟨[78827, 15], [2187, 77683], .contexts [
        ⟨9661, true, false, [], [15]⟩,
        ⟨199, false, false, [78825], []⟩,
        ⟨200, false, false, [78825], []⟩,
        ⟨9654, false, false, [], [1]⟩,
        ⟨9655, false, false, [], [1]⟩,
        ⟨9652, false, false, [], [1]⟩,
        ⟨9653, false, false, [], [1]⟩,
        ⟨9653, false, false, [], [1]⟩,
        ⟨3856, false, false, [2187], []⟩,
        ⟨9669, false, false, [], []⟩,
        ⟨9670, false, false, [], []⟩,
        ⟨9671, false, false, [], []⟩,
        ⟨9672, false, false, [], []⟩
      ]⟩,
    ⟨[78827, 9], [2325, 78821], .contexts [
        ⟨9668, false, false, [], []⟩
      ]⟩,
    ⟨[78827, 9], [2325, 78821], .contexts [
        ⟨9662, false, false, [], []⟩,
        ⟨9674, false, false, [], []⟩,
        ⟨9593, false, false, [], []⟩,
        ⟨9594, false, false, [], []⟩,
        ⟨9594, false, false, [], []⟩
      ]⟩,
    ⟨[2371], [2325, 2331], .source 1250⟩,
    ⟨[78827, 9, 3], [2371, 78821], .contexts [
        ⟨9675, false, false, [], [3]⟩,
        ⟨9584, false, false, [2325, 2328], [78821, 3]⟩,
        ⟨9573, true, false, [2325, 2328, 2327], [3]⟩,
        ⟨9583, false, false, [2325, 2328], [78517, 15, 3]⟩,
        ⟨8163, true, false, [2325, 2328, 2319], [15, 3]⟩,
        ⟨9574, true, false, [2325, 2328], [3, 15, 3]⟩,
        ⟨1555, false, false, [2325, 2328, 78821], []⟩,
        ⟨9576, false, false, [2325, 2328], []⟩,
        ⟨9578, false, false, [2325, 2328], []⟩,
        ⟨9586, true, false, [2325], [78821]⟩,
        ⟨9586, true, false, [2325], [78821]⟩,
        ⟨9585, true, false, [2325], [78821]⟩,
        ⟨9676, true, false, [], [78821]⟩
      ]⟩,
    ⟨[2373], [2371, 2323], .source 1251⟩,
    ⟨[78827], [78827], .contexts []⟩,
    ⟨[78827], [78827], .contexts []⟩,
    ⟨[2375], [2372], .source 1252⟩,
    ⟨[2372], [2372], .contexts []⟩,
    ⟨[2375], [2372], .contexts [
        ⟨9681, false, false, [], []⟩,
        ⟨9682, false, false, [], []⟩,
        ⟨9682, false, false, [], []⟩
      ]⟩,
    ⟨[2377], [2325, 2357], .source 1253⟩,
    ⟨[2377, 78813], [2377, 78813], .contexts []⟩,
    ⟨[2377, 78813], [2377, 78813], .contexts []⟩,
    ⟨[78813, 13], [78813, 13], .contexts []⟩,
    ⟨[2379], [2376], .source 1254⟩,
    ⟨[2376], [2376], .contexts []⟩,
    ⟨[78813, 13], [2379, 78827], .contexts [
        ⟨9687, false, false, [], []⟩,
        ⟨9686, true, false, [2376], [13]⟩,
        ⟨9685, true, false, [2376], [13]⟩,
        ⟨9469, true, false, [], [13]⟩,
        ⟨9684, false, false, [2376], [78815, 9, 13]⟩,
        ⟨9613, true, false, [2376, 2325], [9, 13]⟩,
        ⟨9595, true, false, [2376], [9, 13]⟩,
        ⟨9675, true, false, [2376], [13, 9, 13]⟩,
        ⟨828, false, false, [2376, 78827], []⟩,
        ⟨9679, false, false, [2376], []⟩,
        ⟨9680, false, false, [2376], []⟩,
        ⟨9689, true, false, [], [78827]⟩,
        ⟨9689, true, false, [], [78827]⟩,
        ⟨9688, true, false, [], [78827]⟩
      ]⟩,
    ⟨[2379, 78827], [2379, 78827], .contexts []⟩,
    ⟨[2381], [2379, 2191], .source 1255⟩,
    ⟨[2381, 77571, 13], [78811], .contexts [
        ⟨3099, true, false, [2381], [13]⟩,
        ⟨9692, false, false, [], [77573, 1, 13]⟩,
        ⟨9651, true, false, [2379], [1, 13]⟩,
        ⟨9638, true, false, [2379], [13, 1, 13]⟩,
        ⟨18, true, false, [2379, 78825], [13, 1, 13]⟩,
        ⟨9657, false, false, [2379], [1, 13, 1, 13]⟩,
        ⟨9691, true, false, [], [1, 13, 1, 13]⟩,
        ⟨9691, true, false, [], [1, 13, 1, 13]⟩,
        ⟨9690, true, false, [], [1, 13, 1, 13]⟩,
        ⟨9687, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [78813], []⟩,
        ⟨19, false, false, [78813], []⟩,
        ⟨9484, false, false, [], []⟩,
        ⟨9485, false, false, [], []⟩,
        ⟨9465, false, false, [], []⟩,
        ⟨9465, false, false, [], []⟩
      ]⟩,
    ⟨[77571, 13], [77571, 13], .contexts []⟩,
    ⟨[2383], [2380], .source 1256⟩,
    ⟨[2380], [2380], .contexts []⟩,
    ⟨[2383], [2380], .contexts [
        ⟨9695, false, false, [], []⟩,
        ⟨9696, false, false, [], []⟩,
        ⟨9696, false, false, [], []⟩
      ]⟩,
    ⟨[77571, 13], [2383, 78811], .contexts [
        ⟨9694, false, false, [], []⟩,
        ⟨9693, false, false, [2380], []⟩,
        ⟨9620, false, false, [2380], []⟩,
        ⟨9697, true, false, [], [78811]⟩
      ]⟩,
    ⟨[2381], [2382], .contexts [
        ⟨9695, true, true, [], []⟩
      ]⟩,
    ⟨[2383, 78811], [2383, 78811], .contexts []⟩,
    ⟨[78809, 13], [78809, 13], .contexts []⟩,
    ⟨[2381], [2382], .contexts [
        ⟨9699, false, false, [], []⟩
      ]⟩,
    ⟨[2382], [2382], .contexts []⟩,
    ⟨[78809, 13], [2381, 77569], .contexts [
        ⟨9701, false, false, [], []⟩,
        ⟨9463, true, false, [], [13]⟩,
        ⟨9700, true, false, [2382], [5, 13]⟩,
        ⟨9700, true, false, [2382], [5, 13]⟩,
        ⟨9698, true, false, [2382], [5, 13]⟩,
        ⟨9694, true, false, [2382], [5, 13]⟩,
        ⟨1886, false, false, [2382, 77571], []⟩,
        ⟨3557, false, false, [2382], []⟩,
        ⟨3556, false, false, [2382], []⟩,
        ⟨3559, false, false, [2382], []⟩,
        ⟨9703, true, false, [], [77569]⟩,
        ⟨9703, true, false, [], [77569]⟩,
        ⟨9702, true, false, [], [77569]⟩
      ]⟩,
    ⟨[2381, 77569], [2381, 77569], .contexts []⟩,
    ⟨[2381, 77567], [2381, 77567], .contexts []⟩,
    ⟨[77567, 13], [77567, 13], .contexts []⟩,
    ⟨[77567, 13], [2383, 78807], .contexts [
        ⟨9707, false, false, [], []⟩,
        ⟨9706, true, false, [2380], [13]⟩,
        ⟨3092, true, false, [], [13]⟩,
        ⟨9705, true, false, [2380], [3, 13]⟩,
        ⟨9705, true, false, [2380], [3, 13]⟩,
        ⟨9704, true, false, [2380], [3, 13]⟩,
        ⟨9701, true, false, [2380], [3, 13]⟩,
        ⟨1881, false, false, [2380, 78809], []⟩,
        ⟨9632, false, false, [2380], []⟩,
        ⟨9631, false, false, [2380], []⟩,
        ⟨9633, false, false, [2380], []⟩,
        ⟨9697, true, false, [], [78807]⟩
      ]⟩,
    ⟨[78807, 13], [2381, 77567], .contexts [
        ⟨9708, true, false, [2382], [13]⟩,
        ⟨98, false, false, [2382, 77567], []⟩,
        ⟨9699, true, false, [], [77567]⟩
      ]⟩,
    ⟨[2383, 78807], [2383, 78807], .contexts []⟩,
    ⟨[77565], [755, 77563], .contexts [
        ⟨3087, true, false, [], []⟩,
        ⟨3087, true, false, [], []⟩,
        ⟨3186, true, false, [], []⟩,
        ⟨3574, true, false, [], []⟩,
        ⟨3573, true, false, [752], [1]⟩,
        ⟨18, false, false, [752, 77563], []⟩,
        ⟨3504, true, false, [], [77563]⟩,
        ⟨3570, false, false, [], []⟩,
        ⟨3505, true, false, [], [77563]⟩,
        ⟨3571, false, false, [], []⟩
      ]⟩,
    ⟨[77565], [755, 77563], .contexts [
        ⟨9711, false, false, [], []⟩
      ]⟩,
    ⟨[77567, 1], [755, 77563], .contexts [
        ⟨3574, false, false, [], []⟩,
        ⟨9712, false, false, [], []⟩,
        ⟨3571, false, false, [], []⟩,
        ⟨3571, false, false, [], []⟩
      ]⟩,
    ⟨[2385], [2381, 755], .source 1257⟩,
    ⟨[78805, 13], [2385, 77559], .contexts [
        ⟨9456, true, false, [], [13]⟩,
        ⟨9710, true, false, [2382], [1, 13]⟩,
        ⟨9710, true, false, [2382], [1, 13]⟩,
        ⟨9708, true, false, [2382], [1, 13]⟩,
        ⟨9707, true, false, [2382], [1, 13]⟩,
        ⟨3338, false, false, [2382, 77567], []⟩,
        ⟨389, false, false, [2382, 77567], []⟩,
        ⟨9713, false, false, [2382], [13, 1]⟩,
        ⟨3081, false, false, [2382, 755], [1]⟩,
        ⟨3077, false, false, [2382, 755], []⟩,
        ⟨9702, true, false, [], [755, 77559]⟩,
        ⟨9714, true, false, [], [77559]⟩
      ]⟩,
    ⟨[78829], [77139, 7], .source 39479⟩,
    ⟨[77139, 7], [78829], .contexts [
        ⟨9716, true, false, [], []⟩
      ]⟩,
    ⟨[78829], [78829], .contexts []⟩,
    ⟨[78829], [78829], .contexts []⟩,
    ⟨[315, 77139], [315, 77139], .contexts []⟩,
    ⟨[77139, 13], [1075, 77139], .contexts [
        ⟨4946, false, false, [], []⟩,
        ⟨456, true, false, [], [13]⟩,
        ⟨4944, true, false, [1076], [5, 13]⟩,
        ⟨1886, false, false, [1076, 77137], []⟩,
        ⟨50, false, false, [1076, 77137], []⟩,
        ⟨4945, false, false, [1076], []⟩,
        ⟨2020, false, false, [1076], []⟩,
        ⟨4947, true, false, [], [77139]⟩,
        ⟨4947, true, false, [], [77139]⟩,
        ⟨4940, false, true, [], [77139]⟩
      ]⟩,
    ⟨[1075, 77139], [1075, 77139], .contexts []⟩,
    ⟨[1075, 77139], [1075, 77139], .contexts []⟩,
    ⟨[77139, 13], [1075, 77139], .contexts [
        ⟨4946, false, false, [], []⟩,
        ⟨9721, false, false, [], []⟩,
        ⟨9722, false, false, [], []⟩,
        ⟨9723, false, false, [], []⟩,
        ⟨9723, false, false, [], []⟩
      ]⟩,
    ⟨[78835], [77139, 9], .source 39482⟩,
    ⟨[77139, 9], [78835], .contexts [
        ⟨9725, true, false, [], []⟩
      ]⟩,
    ⟨[78835, 9], [77139], .contexts [
        ⟨9726, true, false, [], [9]⟩,
        ⟨76, false, false, [77139], []⟩,
        ⟨460, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 152. -/
def y322TCContextRaw152 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77139, 9], [78835], .contexts [
        ⟨9726, false, false, [], []⟩
      ]⟩,
    ⟨[78835], [78835], .contexts []⟩,
    ⟨[78835], [78835], .contexts []⟩,
    ⟨[77139, 9], [78835], .contexts [
        ⟨9728, false, false, [], []⟩,
        ⟨9729, false, false, [], []⟩,
        ⟨9730, false, false, [], []⟩,
        ⟨9730, false, false, [], []⟩
      ]⟩,
    ⟨[315, 78835], [315, 78835], .contexts []⟩,
    ⟨[315, 78835], [315, 78835], .contexts []⟩,
    ⟨[78835, 3], [78835, 3], .contexts []⟩,
    ⟨[78835], [78835], .contexts []⟩,
    ⟨[78835, 3], [315, 78835], .contexts [
        ⟨9734, false, false, [], []⟩,
        ⟨9731, true, false, [], [3]⟩,
        ⟨306, false, false, [77139], []⟩,
        ⟨307, false, false, [77139], []⟩,
        ⟨2019, false, false, [], [9]⟩,
        ⟨2021, false, false, [], [9]⟩,
        ⟨9720, false, false, [], [9]⟩,
        ⟨9720, false, false, [], [9]⟩,
        ⟨9726, false, false, [315], []⟩,
        ⟨9732, false, false, [], []⟩,
        ⟨9733, false, false, [], []⟩,
        ⟨9735, false, false, [315], []⟩,
        ⟨2812, true, false, [], [78835]⟩
      ]⟩,
    ⟨[77139, 5], [77137], .contexts [
        ⟨714, false, false, [], []⟩,
        ⟨715, false, false, [], []⟩,
        ⟨457, false, false, [], []⟩,
        ⟨457, false, false, [], []⟩
      ]⟩,
    ⟨[78835, 5], [78835, 5], .contexts []⟩,
    ⟨[78835, 5], [78737], .contexts [
        ⟨9738, false, false, [], []⟩,
        ⟨9731, true, false, [], [5]⟩,
        ⟨1805, false, false, [77139], []⟩,
        ⟨1806, false, false, [77139], []⟩,
        ⟨9737, false, false, [], [9]⟩,
        ⟨9324, false, false, [], []⟩,
        ⟨9325, false, false, [], []⟩,
        ⟨9326, false, false, [], []⟩,
        ⟨9326, false, false, [], []⟩,
        ⟨9328, false, false, [], []⟩,
        ⟨1118, true, false, [], [78737]⟩
      ]⟩,
    ⟨[78837], [77139, 11], .source 39483⟩,
    ⟨[77139, 11], [78837], .contexts [
        ⟨9740, true, false, [], []⟩
      ]⟩,
    ⟨[77139, 11], [78837], .contexts [
        ⟨9741, false, false, [], []⟩
      ]⟩,
    ⟨[78837], [78837], .contexts []⟩,
    ⟨[78837], [78837], .contexts []⟩,
    ⟨[77139, 11], [78837], .contexts [
        ⟨9742, false, false, [], []⟩,
        ⟨9743, false, false, [], []⟩,
        ⟨9744, false, false, [], []⟩,
        ⟨9744, false, false, [], []⟩
      ]⟩,
    ⟨[78837], [78837], .contexts []⟩,
    ⟨[1859, 78531], [1859, 78531], .contexts [
        ⟨8007, false, false, [1859], []⟩
      ]⟩,
    ⟨[1859, 78531], [1859, 78531], .contexts [
        ⟨24, true, false, [], [1859, 78531]⟩
      ]⟩,
    ⟨[78837, 5], [1859, 78531], .contexts [
        ⟨9745, true, false, [], [5]⟩,
        ⟨1083, false, false, [77139], []⟩,
        ⟨1084, false, false, [77139], []⟩,
        ⟨9737, false, false, [], [11]⟩,
        ⟨9107, false, false, [], []⟩,
        ⟨9108, false, false, [], []⟩,
        ⟨9109, false, false, [], []⟩,
        ⟨9109, false, false, [], []⟩,
        ⟨9747, false, false, [], []⟩,
        ⟨9748, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 78837], [1075, 78837], .contexts []⟩,
    ⟨[1075, 78837], [1075, 78837], .contexts []⟩,
    ⟨[78735, 7], [77137], .contexts [
        ⟨9317, true, false, [], [7]⟩,
        ⟨62, false, false, [77137], []⟩,
        ⟨457, false, false, [], []⟩,
        ⟨715, false, false, [], []⟩,
        ⟨457, false, false, [], []⟩,
        ⟨457, false, false, [], []⟩
      ]⟩,
    ⟨[78841], [78735, 11], .source 39485⟩,
    ⟨[78735, 11], [78841], .contexts [
        ⟨9753, true, false, [], []⟩
      ]⟩,
    ⟨[78841], [78841], .contexts []⟩,
    ⟨[78841], [78841], .contexts []⟩,
    ⟨[78841], [78841], .contexts []⟩,
    ⟨[78843], [78735, 15], .source 39486⟩,
    ⟨[78735, 15], [78843], .contexts [
        ⟨9758, true, false, [], []⟩
      ]⟩,
    ⟨[78843], [78843], .contexts []⟩,
    ⟨[78843], [78843], .contexts []⟩,
    ⟨[78735, 15], [78843], .contexts [
        ⟨9759, false, false, [], []⟩,
        ⟨9760, false, false, [], []⟩,
        ⟨9761, false, false, [], []⟩,
        ⟨9761, false, false, [], []⟩
      ]⟩,
    ⟨[78735, 3, 15], [1423, 78539], .contexts [
        ⟨9321, false, false, [], [15]⟩,
        ⟨9321, false, false, [], [15]⟩,
        ⟨9319, true, false, [], [3, 15]⟩,
        ⟨9319, true, false, [], [3, 15]⟩,
        ⟨9318, true, false, [], [3, 15]⟩,
        ⟨9317, true, false, [], [3, 15]⟩,
        ⟨1769, false, false, [77137], [15]⟩,
        ⟨1770, false, false, [77137], [15]⟩,
        ⟨9320, false, false, [], [7, 15]⟩,
        ⟨9207, false, false, [], [15]⟩,
        ⟨9208, false, false, [], [15]⟩,
        ⟨9209, false, false, [], [15]⟩,
        ⟨9209, false, false, [], [15]⟩,
        ⟨1118, true, false, [], [78721, 15]⟩,
        ⟨9208, false, false, [], [15]⟩,
        ⟨9209, false, false, [], [15]⟩,
        ⟨9209, false, false, [], [15]⟩,
        ⟨9224, false, false, [], []⟩,
        ⟨9218, false, false, [], []⟩,
        ⟨9219, false, false, [], []⟩,
        ⟨9219, false, false, [], []⟩
      ]⟩,
    ⟨[78843, 7], [78843, 7], .contexts []⟩,
    ⟨[78845], [78521, 13], .source 39487⟩,
    ⟨[78521, 13], [78845], .contexts [
        ⟨9765, true, false, [], []⟩
      ]⟩,
    ⟨[78845], [78845], .contexts []⟩,
    ⟨[78521, 13], [78845], .contexts [
        ⟨9766, false, false, [], []⟩,
        ⟨9767, false, false, [], []⟩,
        ⟨9767, false, false, [], []⟩
      ]⟩,
    ⟨[78845], [78845], .contexts []⟩,
    ⟨[1941], [1941], .contexts []⟩,
    ⟨[1941], [1941], .contexts []⟩,
    ⟨[78845, 11], [78845, 11], .contexts []⟩,
    ⟨[78845, 11], [1899, 77693], .contexts [
        ⟨9772, false, false, [], []⟩,
        ⟨9768, true, false, [], [11]⟩,
        ⟨137, false, false, [78521], []⟩,
        ⟨138, false, false, [78521], []⟩,
        ⟨7861, false, false, [], [13]⟩,
        ⟨8059, false, false, [], [13]⟩,
        ⟨8058, false, false, [], [13]⟩,
        ⟨8058, false, false, [], [13]⟩,
        ⟨8058, false, false, [], [13]⟩,
        ⟨5703, false, false, [1877], []⟩,
        ⟨8092, true, false, [], [77693]⟩,
        ⟨5701, false, false, [1899], []⟩,
        ⟨8401, true, false, [], [77693]⟩
      ]⟩,
    ⟨[1899, 77693], [1899, 77693], .contexts []⟩,
    ⟨[1899, 77693], [1899, 77693], .contexts []⟩,
    ⟨[78419, 5], [78419, 5], .contexts []⟩,
    ⟨[78419, 5], [1901, 78845], .contexts [
        ⟨9776, false, false, [], []⟩,
        ⟨7706, true, false, [], [5]⟩,
        ⟨7685, true, false, [], [11, 5]⟩,
        ⟨9775, true, false, [1898], [5, 11, 5]⟩,
        ⟨9775, true, false, [1898], [5, 11, 5]⟩,
        ⟨9774, true, false, [1898], [5, 11, 5]⟩,
        ⟨9773, true, false, [1898], [5, 11, 5]⟩,
        ⟨9772, true, false, [1898], [5, 11, 5]⟩,
        ⟨1127, false, false, [1898, 78845], []⟩,
        ⟨9769, false, false, [1898], []⟩,
        ⟨8138, true, false, [], [78845]⟩
      ]⟩,
    ⟨[1901, 78845], [1901, 78845], .contexts []⟩,
    ⟨[1901, 78521], [1901, 78521], .contexts []⟩,
    ⟨[1901, 78553], [1901, 78553], .contexts []⟩,
    ⟨[78553, 13], [1899, 78419], .contexts [
        ⟨9780, true, false, [1900], [13]⟩,
        ⟨8379, true, false, [], [13]⟩,
        ⟨9779, true, false, [1900], [5, 13]⟩,
        ⟨7862, true, false, [], [5, 13]⟩,
        ⟨98, true, false, [78521], [5, 13]⟩,
        ⟨9766, false, false, [], [13, 5, 13]⟩,
        ⟨9778, true, false, [1900], [13, 5, 13]⟩,
        ⟨9778, true, false, [1900], [13, 5, 13]⟩,
        ⟨9777, true, false, [1900], [13, 5, 13]⟩,
        ⟨9776, true, false, [1900], [13, 5, 13]⟩,
        ⟨8416, false, false, [1900, 78419], []⟩,
        ⟨7709, false, false, [1900], []⟩,
        ⟨8168, true, false, [], [78419]⟩
      ]⟩,
    ⟨[1901], [1901], .contexts []⟩,
    ⟨[1901], [1901], .contexts []⟩,
    ⟨[78553], [1899, 78421], .contexts [
        ⟨8135, false, false, [1900], [78553]⟩,
        ⟨9782, false, false, [1900], [78553]⟩,
        ⟨9783, false, false, [1900], [78553]⟩,
        ⟨9780, true, false, [1900], []⟩,
        ⟨8094, false, false, [1900], [78553]⟩,
        ⟨98, true, false, [1900, 1898, 78553], []⟩,
        ⟨9781, false, false, [1900, 1898], [13]⟩,
        ⟨7717, false, false, [1900], []⟩,
        ⟨8140, true, false, [], [78421]⟩
      ]⟩,
    ⟨[1901], [1898], .contexts [
        ⟨8136, false, false, [], []⟩,
        ⟨8137, false, false, [], []⟩,
        ⟨8137, false, false, [], []⟩
      ]⟩,
    ⟨[78553], [1899, 78421], .contexts [
        ⟨9784, false, false, [], []⟩
      ]⟩,
    ⟨[1885], [1885], .contexts [
        ⟨8387, false, false, [], []⟩,
        ⟨8388, false, false, [], []⟩
      ]⟩,
    ⟨[2395], [1901, 1885], .source 1262⟩,
    ⟨[78423], [2395, 77139], .contexts [
        ⟨7725, true, false, [], []⟩,
        ⟨9786, true, false, [1898], [15]⟩,
        ⟨8390, false, false, [1898], []⟩,
        ⟨8384, false, false, [1898], []⟩,
        ⟨9787, true, false, [1898], [77139]⟩,
        ⟨8094, true, false, [], [1885, 77139]⟩,
        ⟨9788, true, false, [], [77139]⟩
      ]⟩,
    ⟨[2395, 77141], [2395, 77141], .contexts []⟩,
    ⟨[2397], [2394], .source 1263⟩]

/-- Exact literal claimed equations and contextual derivations, block 153. -/
def y322TCContextRaw153 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2399], [2395, 1753], .source 1264⟩,
    ⟨[2401], [2398], .source 1265⟩,
    ⟨[2401], [2398], .contexts [
        ⟨9793, false, false, [], []⟩
      ]⟩,
    ⟨[2401], [2398], .contexts [
        ⟨9794, false, false, [], []⟩,
        ⟨24, false, false, [2398], []⟩
      ]⟩,
    ⟨[77267], [2401, 78427], .contexts [
        ⟨9792, false, false, [2398], [77267]⟩,
        ⟨9189, true, false, [2398, 2395], []⟩,
        ⟨9790, true, false, [2398], [3]⟩,
        ⟨9791, true, true, [2398], [77141, 3]⟩,
        ⟨9790, true, false, [2398, 2396, 2394], [3]⟩,
        ⟨459, true, false, [2398, 2396], [3]⟩,
        ⟨9789, true, false, [2398, 2396, 2394], [1, 3]⟩,
        ⟨7733, false, false, [2398, 2396, 2394], [3]⟩,
        ⟨24, true, false, [2398, 2396, 2394], [78425, 3]⟩,
        ⟨9791, true, false, [2398, 2396], [78425, 3]⟩,
        ⟨7736, false, false, [2398], []⟩,
        ⟨7737, false, false, [2398], []⟩,
        ⟨9795, true, false, [], [78427]⟩
      ]⟩,
    ⟨[2399], [2400], .contexts [
        ⟨9793, true, true, [], []⟩
      ]⟩,
    ⟨[2399, 77265], [2399, 77265], .contexts []⟩,
    ⟨[78429], [2399, 77265], .contexts [
        ⟨9795, false, false, [2400], [78429]⟩,
        ⟨7749, true, false, [2400, 2398], []⟩,
        ⟨7748, true, false, [2400, 2398], []⟩,
        ⟨9796, true, false, [2400, 2398, 2400], [5]⟩,
        ⟨9797, true, false, [2400, 2398], [77267, 5]⟩,
        ⟨1220, false, false, [2400], []⟩,
        ⟨9798, false, false, [2400, 2398], []⟩,
        ⟨9797, true, false, [], [77265]⟩
      ]⟩,
    ⟨[2398], [2398], .contexts []⟩,
    ⟨[77265, 9], [2401, 78431], .contexts [
        ⟨9799, true, false, [2398], [9]⟩,
        ⟨7754, false, false, [2398], []⟩,
        ⟨7924, false, false, [2398], []⟩,
        ⟨9800, true, false, [], [78431]⟩,
        ⟨9800, true, false, [], [78431]⟩,
        ⟨9794, true, false, [], [78431]⟩
      ]⟩,
    ⟨[77265, 9], [2401, 78431], .contexts [
        ⟨9801, false, false, [], []⟩
      ]⟩,
    ⟨[2401, 78431], [2401, 78431], .contexts []⟩,
    ⟨[2401, 78431], [2401, 78431], .contexts []⟩,
    ⟨[561, 77271], [561, 77271], .contexts []⟩,
    ⟨[78431, 5], [78431, 5], .contexts []⟩,
    ⟨[77271], [77271], .contexts []⟩,
    ⟨[2399], [2400], .contexts [
        ⟨9797, false, false, [], []⟩
      ]⟩,
    ⟨[2403], [2399, 561], .source 1266⟩,
    ⟨[78431, 5], [2403, 77271], .contexts [
        ⟨9806, false, false, [], []⟩,
        ⟨9804, true, false, [2400], [5]⟩,
        ⟨9804, true, false, [2400], [5]⟩,
        ⟨9803, true, false, [2400], [5]⟩,
        ⟨9802, true, false, [2400], [5]⟩,
        ⟨1219, true, false, [2400], [9, 5]⟩,
        ⟨1219, true, false, [2400], [9, 5]⟩,
        ⟨1412, true, false, [2400], [9, 5]⟩,
        ⟨1411, true, false, [2400], [9, 5]⟩,
        ⟨1672, false, false, [2400, 77267], []⟩,
        ⟨77, false, false, [2400, 77267], []⟩,
        ⟨2905, false, false, [2400], []⟩,
        ⟨9805, false, false, [2400], []⟩,
        ⟨9805, false, false, [2400], []⟩,
        ⟨9807, false, false, [2400, 561], []⟩,
        ⟨9808, true, false, [], [561, 77271]⟩,
        ⟨9809, true, false, [], [77271]⟩
      ]⟩,
    ⟨[2405], [2402], .source 1267⟩,
    ⟨[77271, 5], [2405, 78431], .contexts [
        ⟨9810, true, false, [2402], [5]⟩,
        ⟨49, false, false, [2402, 78431], []⟩,
        ⟨9811, true, false, [], [78431]⟩
      ]⟩,
    ⟨[78745, 3], [78745, 3], .contexts []⟩,
    ⟨[78431], [78431], .contexts []⟩,
    ⟨[2403, 77271], [2403, 77271], .contexts []⟩,
    ⟨[2403, 77271], [2403, 77271], .contexts []⟩,
    ⟨[78431, 5], [2403, 77271], .contexts [
        ⟨9806, false, false, [], []⟩,
        ⟨9810, false, false, [], []⟩,
        ⟨9815, false, false, [], []⟩,
        ⟨9816, false, false, [], []⟩,
        ⟨9816, false, false, [], []⟩
      ]⟩,
    ⟨[78431, 11], [78433], .contexts [
        ⟨7757, false, false, [], []⟩,
        ⟨7923, false, false, [], []⟩,
        ⟨7761, false, false, [], []⟩,
        ⟨7761, false, false, [], []⟩
      ]⟩,
    ⟨[77273, 5], [77273, 5], .contexts []⟩,
    ⟨[78433], [78433], .contexts []⟩,
    ⟨[2402], [2402], .contexts []⟩,
    ⟨[2405], [2402], .contexts [
        ⟨9811, false, false, [], []⟩,
        ⟨9821, false, false, [], []⟩,
        ⟨9821, false, false, [], []⟩
      ]⟩,
    ⟨[77273, 5], [2405, 78433], .contexts [
        ⟨9819, false, false, [], []⟩,
        ⟨1229, true, false, [], [5]⟩,
        ⟨9817, true, false, [2402], [11, 5]⟩,
        ⟨1645, false, false, [2402, 78431], []⟩,
        ⟨91, false, false, [2402, 78431], []⟩,
        ⟨9818, false, false, [2402], []⟩,
        ⟨9820, false, false, [2402], []⟩,
        ⟨9822, true, false, [], [78433]⟩
      ]⟩,
    ⟨[2403], [2404], .contexts [
        ⟨9811, true, true, [], []⟩
      ]⟩,
    ⟨[78745, 3], [2401, 78431], .contexts [
        ⟨9813, false, false, [], []⟩,
        ⟨9813, false, false, [], []⟩,
        ⟨9346, true, false, [], [3]⟩,
        ⟨9346, true, false, [], [3]⟩,
        ⟨9345, true, false, [], [3]⟩,
        ⟨9344, true, false, [], [3]⟩,
        ⟨1216, true, false, [], [9, 3]⟩,
        ⟨1216, true, false, [], [9, 3]⟩,
        ⟨1414, true, false, [], [9, 3]⟩,
        ⟨1413, true, false, [], [9, 3]⟩,
        ⟨1010, false, false, [77265], []⟩,
        ⟨77, false, false, [77265], []⟩,
        ⟨9802, false, false, [], []⟩,
        ⟨9803, false, false, [], []⟩,
        ⟨9804, false, false, [], []⟩,
        ⟨9804, false, false, [], []⟩,
        ⟨9814, false, false, [2401], []⟩,
        ⟨24, true, false, [], [2401, 78431]⟩,
        ⟨9803, false, false, [], []⟩,
        ⟨9804, false, false, [], []⟩,
        ⟨9804, false, false, [], []⟩
      ]⟩,
    ⟨[78433, 3], [78433, 3], .contexts []⟩,
    ⟨[2400], [2400], .contexts []⟩,
    ⟨[78433, 3], [2399, 78747], .contexts [
        ⟨9826, false, false, [], []⟩,
        ⟨7757, true, false, [], [3]⟩,
        ⟨9825, true, false, [2400], [11, 3]⟩,
        ⟨976, false, false, [2400, 78745], []⟩,
        ⟨91, false, false, [2400, 78745], []⟩,
        ⟨9364, false, false, [2400], []⟩,
        ⟨9368, false, false, [2400], []⟩,
        ⟨9827, true, false, [], [78747]⟩,
        ⟨9827, true, false, [], [78747]⟩,
        ⟨9808, true, false, [], [78747]⟩
      ]⟩,
    ⟨[2405, 78433], [2405, 78433], .contexts []⟩,
    ⟨[78435, 5], [78435, 5], .contexts []⟩,
    ⟨[77275], [77275], .contexts []⟩,
    ⟨[2404], [2404], .contexts []⟩,
    ⟨[2403], [2404], .contexts [
        ⟨9824, false, false, [], []⟩,
        ⟨9832, false, false, [], []⟩,
        ⟨9832, false, false, [], []⟩
      ]⟩,
    ⟨[2399, 78747], [2399, 78747], .contexts []⟩,
    ⟨[2399, 78747], [2399, 78747], .contexts []⟩,
    ⟨[2407], [2399, 283], .source 1268⟩,
    ⟨[2409], [2407, 2401], .source 1269⟩,
    ⟨[78433, 1], [78435], .contexts [
        ⟨7760, false, false, [], []⟩
      ]⟩,
    ⟨[2409, 78435, 3], [78435], .contexts [
        ⟨7760, true, false, [2409], [3]⟩,
        ⟨9837, false, false, [], [78433, 1, 3]⟩,
        ⟨9793, false, false, [2407], [78433, 1, 3]⟩,
        ⟨35, true, false, [2407, 2398, 78433], [1, 3]⟩,
        ⟨9828, false, false, [2407, 2398], [3, 1, 3]⟩,
        ⟨9836, false, false, [], [78747, 3, 1, 3]⟩,
        ⟨9369, true, false, [2399], [3, 1, 3]⟩,
        ⟨9835, true, false, [], [1, 3, 1, 3]⟩,
        ⟨9835, true, false, [], [1, 3, 1, 3]⟩,
        ⟨9834, true, false, [], [1, 3, 1, 3]⟩,
        ⟨9828, true, false, [], [1, 3, 1, 3]⟩,
        ⟨9826, true, false, [], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [78433], []⟩,
        ⟨19, false, false, [78433], []⟩,
        ⟨9838, false, false, [], []⟩,
        ⟨7922, false, false, [], []⟩,
        ⟨7765, false, false, [], []⟩,
        ⟨7765, false, false, [], []⟩
      ]⟩,
    ⟨[78435, 3], [78435, 3], .contexts []⟩,
    ⟨[78435], [78435], .contexts []⟩,
    ⟨[2411], [2408], .source 1270⟩,
    ⟨[2408], [2408], .contexts []⟩,
    ⟨[2403, 77275], [2403, 77275], .contexts []⟩,
    ⟨[78435, 5], [2403, 77275], .contexts [
        ⟨9830, false, false, [], []⟩,
        ⟨9830, false, false, [], []⟩,
        ⟨7760, true, false, [], [5]⟩,
        ⟨9829, true, false, [2404], [1, 5]⟩,
        ⟨9829, true, false, [2404], [1, 5]⟩,
        ⟨9823, true, false, [2404], [1, 5]⟩,
        ⟨9819, true, false, [2404], [1, 5]⟩,
        ⟨1509, false, false, [2404, 77273], []⟩,
        ⟨19, false, false, [2404, 77273], []⟩,
        ⟨1232, false, false, [2404], []⟩,
        ⟨1404, false, false, [2404], []⟩,
        ⟨1237, false, false, [2404], []⟩,
        ⟨1237, false, false, [2404], []⟩,
        ⟨9831, false, false, [2404], []⟩,
        ⟨9833, true, false, [], [77275]⟩,
        ⟨9844, false, false, [], []⟩,
        ⟨9844, false, false, [], []⟩
      ]⟩,
    ⟨[77277, 5], [77277, 5], .contexts []⟩,
    ⟨[78437], [78437], .contexts []⟩,
    ⟨[2411, 78435], [2411, 78435], .contexts []⟩,
    ⟨[2405, 78437], [2405, 78437], .contexts []⟩,
    ⟨[77277, 5, 15], [2405, 78439], .contexts [
        ⟨9846, false, false, [], [15]⟩,
        ⟨9846, false, false, [], [15]⟩,
        ⟨1236, true, false, [], [5, 15]⟩,
        ⟨9845, true, false, [2402], [13, 5, 15]⟩,
        ⟨1578, false, false, [2402, 78435], [15]⟩,
        ⟨108, false, false, [2402, 78435], [15]⟩,
        ⟨7764, false, false, [2402], [15]⟩,
        ⟨7921, false, false, [2402], [15]⟩,
        ⟨7768, false, false, [2402], [15]⟩,
        ⟨7768, false, false, [2402], [15]⟩,
        ⟨9847, false, false, [2402], [15]⟩,
        ⟨9822, true, false, [], [78437, 15]⟩,
        ⟨9849, false, false, [], [15]⟩,
        ⟨9849, false, false, [], [15]⟩,
        ⟨7767, false, false, [2405], []⟩
      ]⟩,
    ⟨[78439, 5], [78439, 5], .contexts []⟩,
    ⟨[78439, 5], [2403, 77279], .contexts [
        ⟨9851, false, false, [], []⟩,
        ⟨9850, true, false, [2404], [5]⟩,
        ⟨2006, false, false, [2404, 77277], []⟩,
        ⟨20, false, false, [2404, 77277], []⟩,
        ⟨1239, false, false, [2404], []⟩,
        ⟨1402, false, false, [2404], []⟩,
        ⟨1243, false, false, [2404], []⟩,
        ⟨1243, false, false, [2404], []⟩,
        ⟨9833, true, false, [], [77279]⟩
      ]⟩,
    ⟨[2403, 77279], [2403, 77279], .contexts []⟩,
    ⟨[2403, 77279], [2403, 77279], .contexts []⟩,
    ⟨[78847], [78281, 13], .source 39488⟩]

/-- Exact literal claimed equations and contextual derivations, block 154. -/
def y322TCContextRaw154 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78281, 13], [78847], .contexts [
        ⟨9855, true, false, [], []⟩
      ]⟩,
    ⟨[78847], [78847], .contexts []⟩,
    ⟨[2207, 78243], [2207, 78243], .contexts []⟩,
    ⟨[2207, 78241], [2207, 78241], .contexts []⟩,
    ⟨[2207, 78241], [2207, 78241], .contexts []⟩,
    ⟨[78847, 5], [78847, 5], .contexts []⟩,
    ⟨[2207], [2207], .contexts [
        ⟨24, false, false, [], [2207]⟩
      ]⟩,
    ⟨[78847, 5], [2207, 78241], .contexts [
        ⟨9861, false, false, [], []⟩,
        ⟨9857, true, false, [], [5]⟩,
        ⟨9857, true, false, [], [5]⟩,
        ⟨9856, true, false, [], [5]⟩,
        ⟨116, false, false, [78281], []⟩,
        ⟨117, false, false, [78281], []⟩,
        ⟨9179, true, false, [2204], [5, 13]⟩,
        ⟨49, false, false, [2204, 78243], [13]⟩,
        ⟨9180, true, false, [], [78243, 13]⟩,
        ⟨9858, false, false, [], [13]⟩,
        ⟨9858, false, false, [], [13]⟩,
        ⟨6512, false, false, [2207], []⟩,
        ⟨9859, false, false, [], []⟩,
        ⟨9860, false, false, [], []⟩,
        ⟨6687, false, false, [2207], []⟩,
        ⟨9862, true, false, [], [78241]⟩
      ]⟩,
    ⟨[2205], [2206], .contexts [
        ⟨9180, true, true, [], []⟩
      ]⟩,
    ⟨[78241, 5], [2205, 78847], .contexts [
        ⟨9863, true, false, [2206], [5]⟩,
        ⟨49, false, false, [2206, 78847], []⟩,
        ⟨9864, true, false, [], [78847]⟩
      ]⟩,
    ⟨[78847, 5], [2207, 78241], .contexts [
        ⟨9861, false, false, [], []⟩,
        ⟨9863, false, false, [], []⟩,
        ⟨9859, false, false, [], []⟩,
        ⟨9860, false, false, [], []⟩,
        ⟨9860, false, false, [], []⟩
      ]⟩,
    ⟨[2419], [2207, 1459], .source 1274⟩,
    ⟨[2421], [2419, 2205], .source 1275⟩,
    ⟨[78847, 15], [78847, 15], .contexts []⟩,
    ⟨[2423], [2420], .source 1276⟩,
    ⟨[2420], [2420], .contexts []⟩,
    ⟨[78847, 15], [2423, 78847], .contexts [
        ⟨9869, false, false, [], []⟩,
        ⟨9868, false, false, [2420], [78847, 15]⟩,
        ⟨9865, true, false, [2420, 2419], [15]⟩,
        ⟨9867, false, false, [2420], [78241, 5, 15]⟩,
        ⟨6690, true, false, [2420, 2207], [5, 15]⟩,
        ⟨9866, true, false, [2420], [15, 5, 15]⟩,
        ⟨1504, false, false, [2420, 78847], []⟩,
        ⟨9871, true, false, [], [78847]⟩,
        ⟨9871, true, false, [], [78847]⟩,
        ⟨9870, true, false, [], [78847]⟩
      ]⟩,
    ⟨[78849], [78847, 1], .source 39489⟩,
    ⟨[78847, 1], [78849], .contexts [
        ⟨9873, true, false, [], []⟩
      ]⟩,
    ⟨[78849, 1], [78847], .contexts [
        ⟨9874, true, false, [], [1]⟩,
        ⟨18, false, false, [78847], []⟩,
        ⟨9857, false, false, [], []⟩
      ]⟩,
    ⟨[78849], [78849], .contexts []⟩,
    ⟨[78847, 1], [78849], .contexts [
        ⟨9874, false, false, [], []⟩,
        ⟨9876, false, false, [], []⟩,
        ⟨9876, false, false, [], []⟩
      ]⟩,
    ⟨[2207, 78239], [2207, 78239], .contexts []⟩,
    ⟨[2207, 78239], [2207, 78239], .contexts []⟩,
    ⟨[78849, 5], [78849, 5], .contexts []⟩,
    ⟨[78849, 5], [2207, 78239], .contexts [
        ⟨9880, false, false, [], []⟩,
        ⟨9877, true, false, [], [5]⟩,
        ⟨165, false, false, [78847], []⟩,
        ⟨166, false, false, [78847], []⟩,
        ⟨9866, false, false, [], [1]⟩,
        ⟨6508, false, false, [2207], []⟩,
        ⟨9878, false, false, [], []⟩,
        ⟨9879, false, false, [], []⟩,
        ⟨6698, false, false, [2207], []⟩,
        ⟨9862, true, false, [], [78239]⟩
      ]⟩,
    ⟨[78239, 5], [2205, 78849], .contexts [
        ⟨9881, true, false, [2206], [5]⟩,
        ⟨49, false, false, [2206, 78849], []⟩,
        ⟨9864, true, false, [], [78849]⟩
      ]⟩,
    ⟨[2423, 78847], [2423, 78847], .contexts []⟩,
    ⟨[2423, 78849], [2423, 78849], .contexts []⟩,
    ⟨[2423, 78849], [2423, 78849], .contexts []⟩,
    ⟨[78849, 15], [78849, 15], .contexts []⟩,
    ⟨[78849], [78849], .contexts []⟩,
    ⟨[2423], [2423], .contexts [
        ⟨24, false, false, [], [2423]⟩
      ]⟩,
    ⟨[78851], [78849, 3], .source 39490⟩,
    ⟨[78849, 3], [78851], .contexts [
        ⟨9889, true, false, [], []⟩
      ]⟩,
    ⟨[78849, 3], [78851], .contexts [
        ⟨9890, false, false, [], []⟩
      ]⟩,
    ⟨[78851], [78851], .contexts []⟩,
    ⟨[78851], [78851], .contexts []⟩,
    ⟨[78849, 3], [78851], .contexts [
        ⟨9891, false, false, [], []⟩,
        ⟨9892, false, false, [], []⟩,
        ⟨9893, false, false, [], []⟩,
        ⟨9893, false, false, [], []⟩
      ]⟩,
    ⟨[2425], [2207, 1917], .source 1277⟩,
    ⟨[2427], [2425, 2205], .source 1278⟩,
    ⟨[2427, 78851], [2427, 78851], .contexts []⟩,
    ⟨[2427, 78851], [2427, 78851], .contexts []⟩,
    ⟨[78851], [78851], .contexts []⟩,
    ⟨[78851, 5], [2427, 78851], .contexts [
        ⟨9894, true, false, [], [5]⟩,
        ⟨1479, false, false, [78849], []⟩,
        ⟨1481, false, false, [78849], []⟩,
        ⟨9880, false, false, [], [3, 5, 3]⟩,
        ⟨9881, false, false, [], [3, 5, 3]⟩,
        ⟨9878, false, false, [], [3, 5, 3]⟩,
        ⟨9879, false, false, [], [3, 5, 3]⟩,
        ⟨9879, false, false, [], [3, 5, 3]⟩,
        ⟨8119, false, false, [2207], [5, 3]⟩,
        ⟨9895, true, false, [], [78239, 5, 3]⟩,
        ⟨9882, false, false, [2425], [3]⟩,
        ⟨9896, true, false, [], [78849, 3]⟩,
        ⟨9890, false, false, [2427], []⟩,
        ⟨9897, false, false, [], []⟩,
        ⟨9898, false, false, [], []⟩,
        ⟨9899, false, false, [2427], []⟩
      ]⟩,
    ⟨[78849, 15, 3], [2423, 78851], .contexts [
        ⟨9886, false, false, [], [3]⟩,
        ⟨9886, false, false, [], [3]⟩,
        ⟨9877, true, false, [], [15, 3]⟩,
        ⟨199, false, false, [78847], [3]⟩,
        ⟨200, false, false, [78847], [3]⟩,
        ⟨9869, false, false, [], [1, 3]⟩,
        ⟨9872, false, false, [], [1, 3]⟩,
        ⟨9883, false, false, [], [1, 3]⟩,
        ⟨9883, false, false, [], [1, 3]⟩,
        ⟨9874, false, false, [2423], [3]⟩,
        ⟨9884, false, false, [], [3]⟩,
        ⟨9885, false, false, [], [3]⟩,
        ⟨9887, false, false, [2423], [3]⟩,
        ⟨9888, true, false, [], [78849, 3]⟩,
        ⟨9884, false, false, [], [3]⟩,
        ⟨9885, false, false, [], [3]⟩,
        ⟨9885, false, false, [], [3]⟩,
        ⟨9890, false, false, [2423], []⟩
      ]⟩,
    ⟨[78853], [78851, 1], .source 39491⟩,
    ⟨[78851, 1], [78853], .contexts [
        ⟨9902, true, false, [], []⟩
      ]⟩,
    ⟨[78853], [78853], .contexts []⟩,
    ⟨[78853], [78853], .contexts []⟩,
    ⟨[78855], [78853, 9], .source 39492⟩,
    ⟨[78855], [78855], .contexts []⟩,
    ⟨[78857], [78855, 11], .source 39493⟩,
    ⟨[78857], [78857], .contexts []⟩,
    ⟨[78859], [78857, 1], .source 39494⟩,
    ⟨[78859], [78859], .contexts []⟩,
    ⟨[78861], [78859, 13], .source 39495⟩,
    ⟨[78861], [78861], .contexts []⟩,
    ⟨[78863], [78861, 15], .source 39496⟩,
    ⟨[78863], [78863], .contexts []⟩,
    ⟨[78865], [78863, 1], .source 39497⟩,
    ⟨[78865], [78865], .contexts []⟩,
    ⟨[78867], [78865, 3], .source 39498⟩,
    ⟨[78869], [78867, 5], .source 39499⟩]

/-- Exact literal claimed equations and contextual derivations, block 155. -/
def y322TCContextRaw155 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78867], [78867], .contexts []⟩,
    ⟨[78869], [78869], .contexts []⟩,
    ⟨[78871], [78869, 1], .source 39500⟩,
    ⟨[78873], [78871, 9], .source 39501⟩,
    ⟨[78871], [78871], .contexts []⟩,
    ⟨[78875], [78873, 11], .source 39502⟩,
    ⟨[78873], [78873], .contexts []⟩,
    ⟨[78877], [78875, 1], .source 39503⟩,
    ⟨[78875], [78875], .contexts []⟩,
    ⟨[78879], [78877, 13], .source 39504⟩,
    ⟨[78877], [78877], .contexts []⟩,
    ⟨[78881], [78879, 15], .source 39505⟩,
    ⟨[78879], [78879], .contexts []⟩,
    ⟨[78883], [78881, 1], .source 39506⟩,
    ⟨[78881], [78881], .contexts []⟩,
    ⟨[78885], [78883, 3], .source 39507⟩,
    ⟨[78883], [78883], .contexts []⟩,
    ⟨[78887], [78885, 5], .source 39508⟩,
    ⟨[78885], [78885], .contexts []⟩,
    ⟨[78889], [78887, 1], .source 39509⟩,
    ⟨[78887], [78887], .contexts []⟩,
    ⟨[78891], [78889, 9], .source 39510⟩,
    ⟨[78889], [78889], .contexts []⟩,
    ⟨[78893], [78891, 11], .source 39511⟩,
    ⟨[78891], [78891], .contexts []⟩,
    ⟨[78895], [78893, 1], .source 39512⟩,
    ⟨[78893], [78893], .contexts []⟩,
    ⟨[78897], [78895, 13], .source 39513⟩,
    ⟨[78895], [78895], .contexts []⟩,
    ⟨[78899], [78897, 15], .source 39514⟩,
    ⟨[78897], [78897], .contexts []⟩,
    ⟨[78901], [78899, 1], .source 39515⟩,
    ⟨[78899], [78899], .contexts []⟩,
    ⟨[78903], [78901, 3], .source 39516⟩,
    ⟨[78901], [78901], .contexts []⟩,
    ⟨[78905], [78903, 5], .source 39517⟩,
    ⟨[78903], [78903], .contexts []⟩,
    ⟨[78907], [78905, 1], .source 39518⟩,
    ⟨[78905], [78905], .contexts []⟩,
    ⟨[78909], [78907, 9], .source 39519⟩,
    ⟨[78907], [78907], .contexts []⟩,
    ⟨[78911], [78909, 11], .source 39520⟩,
    ⟨[78909], [78909], .contexts []⟩,
    ⟨[78913], [78911, 1], .source 39521⟩,
    ⟨[78911], [78911], .contexts []⟩,
    ⟨[78915], [78913, 13], .source 39522⟩,
    ⟨[78913], [78913], .contexts []⟩,
    ⟨[78917], [78915, 15], .source 39523⟩,
    ⟨[78915], [78915], .contexts []⟩,
    ⟨[78919], [78917, 1], .source 39524⟩,
    ⟨[78917], [78917], .contexts []⟩,
    ⟨[78921], [78919, 3], .source 39525⟩,
    ⟨[78919], [78919], .contexts []⟩,
    ⟨[78923], [78921, 5], .source 39526⟩,
    ⟨[78921], [78921], .contexts []⟩,
    ⟨[78925], [78923, 1], .source 39527⟩,
    ⟨[78923], [78923], .contexts []⟩,
    ⟨[78927], [78925, 9], .source 39528⟩,
    ⟨[78925], [78925], .contexts []⟩,
    ⟨[78929], [78927, 11], .source 39529⟩,
    ⟨[78927], [78927], .contexts []⟩,
    ⟨[78931], [78929, 1], .source 39530⟩,
    ⟨[78929], [78929], .contexts []⟩,
    ⟨[78933], [78931, 13], .source 39531⟩]

/-- Exact literal claimed equations and contextual derivations, block 156. -/
def y322TCContextRaw156 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78931], [78931], .contexts []⟩,
    ⟨[78935], [78933, 15], .source 39532⟩,
    ⟨[78933], [78933], .contexts []⟩,
    ⟨[78937], [78935, 1], .source 39533⟩,
    ⟨[78935], [78935], .contexts []⟩,
    ⟨[78939], [78937, 3], .source 39534⟩,
    ⟨[78937], [78937], .contexts []⟩,
    ⟨[78941], [78939, 5], .source 39535⟩,
    ⟨[78939], [78939], .contexts []⟩,
    ⟨[78943], [78941, 1], .source 39536⟩,
    ⟨[78941], [78941], .contexts []⟩,
    ⟨[78945], [78943, 9], .source 39537⟩,
    ⟨[78943], [78943], .contexts []⟩,
    ⟨[78947], [78945, 11], .source 39538⟩,
    ⟨[78945], [78945], .contexts []⟩,
    ⟨[78949], [78947, 1], .source 39539⟩,
    ⟨[78947], [78947], .contexts []⟩,
    ⟨[78951], [78949, 13], .source 39540⟩,
    ⟨[78949], [78949], .contexts []⟩,
    ⟨[78953], [78951, 15], .source 39541⟩,
    ⟨[78951], [78951], .contexts []⟩,
    ⟨[78955], [78953, 1], .source 39542⟩,
    ⟨[78953], [78953], .contexts []⟩,
    ⟨[78957], [78955, 3], .source 39543⟩,
    ⟨[78955], [78955], .contexts []⟩,
    ⟨[78959], [78957, 5], .source 39544⟩,
    ⟨[78957], [78957], .contexts []⟩,
    ⟨[78961], [78959, 1], .source 39545⟩,
    ⟨[78959, 1], [78961], .contexts [
        ⟨10011, true, false, [], []⟩
      ]⟩,
    ⟨[78959], [78959], .contexts []⟩,
    ⟨[78961, 1], [78959], .contexts [
        ⟨10012, true, false, [], [1]⟩,
        ⟨18, false, false, [78959], []⟩,
        ⟨10013, false, false, [], []⟩
      ]⟩,
    ⟨[78963], [78961, 9], .source 39546⟩,
    ⟨[78961, 9], [78963], .contexts [
        ⟨10015, true, false, [], []⟩
      ]⟩,
    ⟨[78961], [78961], .contexts []⟩,
    ⟨[78963, 9], [78961], .contexts [
        ⟨10016, true, false, [], [9]⟩,
        ⟨76, false, false, [78961], []⟩,
        ⟨10017, false, false, [], []⟩
      ]⟩,
    ⟨[78965], [78963, 11], .source 39547⟩,
    ⟨[78963], [78963], .contexts []⟩,
    ⟨[78965, 11], [78963], .contexts [
        ⟨10019, false, false, [], [11]⟩,
        ⟨90, false, false, [78963], []⟩,
        ⟨10020, false, false, [], []⟩
      ]⟩,
    ⟨[78967], [78965, 1], .source 39548⟩,
    ⟨[78965], [78965], .contexts []⟩,
    ⟨[78967, 1], [78965], .contexts [
        ⟨10022, false, false, [], [1]⟩,
        ⟨18, false, false, [78965], []⟩,
        ⟨10023, false, false, [], []⟩
      ]⟩,
    ⟨[78969], [78967, 13], .source 39549⟩,
    ⟨[78967], [78967], .contexts []⟩,
    ⟨[78969, 13], [78967], .contexts [
        ⟨10025, false, false, [], [13]⟩,
        ⟨98, false, false, [78967], []⟩,
        ⟨10026, false, false, [], []⟩
      ]⟩,
    ⟨[78971], [78969, 15], .source 39550⟩,
    ⟨[78969], [78969], .contexts []⟩,
    ⟨[78971, 15], [78969], .contexts [
        ⟨10028, false, false, [], [15]⟩,
        ⟨3, false, false, [78969], []⟩,
        ⟨10029, false, false, [], []⟩
      ]⟩,
    ⟨[78973], [78971, 1], .source 39551⟩,
    ⟨[78971], [78971], .contexts []⟩,
    ⟨[78973, 1], [78971], .contexts [
        ⟨10031, false, false, [], [1]⟩,
        ⟨18, false, false, [78971], []⟩,
        ⟨10032, false, false, [], []⟩
      ]⟩,
    ⟨[78975], [78973, 3], .source 39552⟩,
    ⟨[78973], [78973], .contexts []⟩,
    ⟨[78975, 3], [78973], .contexts [
        ⟨10034, false, false, [], [3]⟩,
        ⟨35, false, false, [78973], []⟩,
        ⟨10035, false, false, [], []⟩
      ]⟩,
    ⟨[78977], [78975, 5], .source 39553⟩,
    ⟨[78975], [78975], .contexts []⟩,
    ⟨[78977, 5], [78975], .contexts [
        ⟨10037, false, false, [], [5]⟩,
        ⟨49, false, false, [78975], []⟩,
        ⟨10038, false, false, [], []⟩
      ]⟩,
    ⟨[78979], [78977, 1], .source 39554⟩,
    ⟨[78977], [78977], .contexts []⟩,
    ⟨[78979, 1], [78977], .contexts [
        ⟨10040, false, false, [], [1]⟩,
        ⟨18, false, false, [78977], []⟩,
        ⟨10041, false, false, [], []⟩
      ]⟩,
    ⟨[78981], [78979, 9], .source 39555⟩,
    ⟨[78979], [78979], .contexts []⟩,
    ⟨[78981, 9], [78979], .contexts [
        ⟨10043, false, false, [], [9]⟩,
        ⟨76, false, false, [78979], []⟩,
        ⟨10044, false, false, [], []⟩
      ]⟩,
    ⟨[78983], [78981, 11], .source 39556⟩,
    ⟨[78981, 11], [78983], .contexts [
        ⟨10046, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 157. -/
def y322TCContextRaw157 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78981], [78981], .contexts []⟩,
    ⟨[78983, 11], [78981], .contexts [
        ⟨10047, true, false, [], [11]⟩,
        ⟨90, false, false, [78981], []⟩,
        ⟨10048, false, false, [], []⟩
      ]⟩,
    ⟨[78985], [78983, 1], .source 39557⟩,
    ⟨[78983, 1], [78985], .contexts [
        ⟨10050, true, false, [], []⟩
      ]⟩,
    ⟨[78985, 1], [78983], .contexts [
        ⟨10051, true, false, [], [1]⟩,
        ⟨18, false, false, [78983], []⟩
      ]⟩,
    ⟨[78985], [78985], .contexts []⟩,
    ⟨[78979], [78979], .contexts []⟩,
    ⟨[78977], [78977], .contexts []⟩,
    ⟨[78975], [78975], .contexts []⟩,
    ⟨[78973], [78973], .contexts []⟩,
    ⟨[78983, 11, 9, 1, 5, 3], [78973], .contexts [
        ⟨10049, false, false, [], [9, 1, 5, 3]⟩,
        ⟨10048, false, false, [], [9, 1, 5, 3]⟩,
        ⟨10048, false, false, [], [9, 1, 5, 3]⟩,
        ⟨10045, false, false, [], [1, 5, 3]⟩,
        ⟨10054, false, false, [], [1, 5, 3]⟩,
        ⟨10044, false, false, [], [1, 5, 3]⟩,
        ⟨10044, false, false, [], [1, 5, 3]⟩,
        ⟨10042, false, false, [], [5, 3]⟩,
        ⟨10055, false, false, [], [5, 3]⟩,
        ⟨10041, false, false, [], [5, 3]⟩,
        ⟨10041, false, false, [], [5, 3]⟩,
        ⟨10039, false, false, [], [3]⟩,
        ⟨10056, false, false, [], [3]⟩,
        ⟨10038, false, false, [], [3]⟩,
        ⟨10038, false, false, [], [3]⟩,
        ⟨10036, false, false, [], []⟩,
        ⟨10057, false, false, [], []⟩,
        ⟨10035, false, false, [], []⟩,
        ⟨10035, false, false, [], []⟩
      ]⟩,
    ⟨[78971], [78971], .contexts []⟩,
    ⟨[78969], [78969], .contexts []⟩,
    ⟨[78967], [78967], .contexts []⟩,
    ⟨[78965], [78965], .contexts []⟩,
    ⟨[78963], [78963], .contexts []⟩,
    ⟨[78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [78963], .contexts [
        ⟨10058, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨10033, false, false, [], [15, 13, 1, 11]⟩,
        ⟨10059, false, false, [], [15, 13, 1, 11]⟩,
        ⟨10032, false, false, [], [15, 13, 1, 11]⟩,
        ⟨10032, false, false, [], [15, 13, 1, 11]⟩,
        ⟨10030, false, false, [], [13, 1, 11]⟩,
        ⟨10060, false, false, [], [13, 1, 11]⟩,
        ⟨10029, false, false, [], [13, 1, 11]⟩,
        ⟨10029, false, false, [], [13, 1, 11]⟩,
        ⟨10027, false, false, [], [1, 11]⟩,
        ⟨10061, false, false, [], [1, 11]⟩,
        ⟨10026, false, false, [], [1, 11]⟩,
        ⟨10026, false, false, [], [1, 11]⟩,
        ⟨10024, false, false, [], [11]⟩,
        ⟨10062, false, false, [], [11]⟩,
        ⟨10023, false, false, [], [11]⟩,
        ⟨10023, false, false, [], [11]⟩,
        ⟨10021, false, false, [], []⟩,
        ⟨10063, false, false, [], []⟩,
        ⟨10020, false, false, [], []⟩,
        ⟨10020, false, false, [], []⟩
      ]⟩,
    ⟨[78961], [78961], .contexts []⟩,
    ⟨[78961, 1], [78959], .contexts [
        ⟨10014, false, false, [], []⟩
      ]⟩,
    ⟨[78959], [78959], .contexts []⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [78953], .contexts [
        ⟨10064, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨10018, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10065, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10017, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10017, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10066, false, false, [], [5, 3, 1]⟩,
        ⟨10067, false, false, [], [5, 3, 1]⟩,
        ⟨10013, false, false, [], [5, 3, 1]⟩,
        ⟨10013, false, false, [], [5, 3, 1]⟩,
        ⟨10009, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78957], [3, 1]⟩,
        ⟨10010, false, false, [], [3, 1]⟩,
        ⟨10010, false, false, [], [3, 1]⟩,
        ⟨10010, false, false, [], [3, 1]⟩,
        ⟨10007, false, false, [], [3, 1]⟩,
        ⟨35, false, false, [78955], [1]⟩,
        ⟨10008, false, false, [], [1]⟩,
        ⟨10008, false, false, [], [1]⟩,
        ⟨10008, false, false, [], [1]⟩,
        ⟨10005, false, false, [], [1]⟩,
        ⟨18, false, false, [78953], []⟩,
        ⟨10006, false, false, [], []⟩,
        ⟨10006, false, false, [], []⟩,
        ⟨10006, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [78945], .contexts [
        ⟨10068, false, false, [], [15, 13, 1, 11]⟩,
        ⟨10003, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [78951], [13, 1, 11]⟩,
        ⟨10004, false, false, [], [13, 1, 11]⟩,
        ⟨10004, false, false, [], [13, 1, 11]⟩,
        ⟨10004, false, false, [], [13, 1, 11]⟩,
        ⟨10001, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78949], [1, 11]⟩,
        ⟨10002, false, false, [], [1, 11]⟩,
        ⟨10002, false, false, [], [1, 11]⟩,
        ⟨10002, false, false, [], [1, 11]⟩,
        ⟨9999, false, false, [], [1, 11]⟩,
        ⟨18, false, false, [78947], [11]⟩,
        ⟨10000, false, false, [], [11]⟩,
        ⟨10000, false, false, [], [11]⟩,
        ⟨10000, false, false, [], [11]⟩,
        ⟨9997, false, false, [], [11]⟩,
        ⟨90, false, false, [78945], []⟩,
        ⟨9998, false, false, [], []⟩,
        ⟨9998, false, false, [], []⟩,
        ⟨9998, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [78937], .contexts [
        ⟨10069, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9995, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [78943], [1, 5, 3]⟩,
        ⟨9996, false, false, [], [1, 5, 3]⟩,
        ⟨9996, false, false, [], [1, 5, 3]⟩,
        ⟨9996, false, false, [], [1, 5, 3]⟩,
        ⟨9993, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [78941], [5, 3]⟩,
        ⟨9994, false, false, [], [5, 3]⟩,
        ⟨9994, false, false, [], [5, 3]⟩,
        ⟨9994, false, false, [], [5, 3]⟩,
        ⟨9991, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [78939], [3]⟩,
        ⟨9992, false, false, [], [3]⟩,
        ⟨9992, false, false, [], [3]⟩,
        ⟨9992, false, false, [], [3]⟩,
        ⟨9989, false, false, [], [3]⟩,
        ⟨35, false, false, [78937], []⟩,
        ⟨9990, false, false, [], []⟩,
        ⟨9990, false, false, [], []⟩,
        ⟨9990, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [78929], .contexts [
        ⟨10070, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9987, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [78935], [15, 13, 1]⟩,
        ⟨9988, false, false, [], [15, 13, 1]⟩,
        ⟨9988, false, false, [], [15, 13, 1]⟩,
        ⟨9988, false, false, [], [15, 13, 1]⟩,
        ⟨9985, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [78933], [13, 1]⟩,
        ⟨9986, false, false, [], [13, 1]⟩,
        ⟨9986, false, false, [], [13, 1]⟩,
        ⟨9986, false, false, [], [13, 1]⟩,
        ⟨9983, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [78931], [1]⟩,
        ⟨9984, false, false, [], [1]⟩,
        ⟨9984, false, false, [], [1]⟩,
        ⟨9984, false, false, [], [1]⟩,
        ⟨9981, false, false, [], [1]⟩,
        ⟨18, false, false, [78929], []⟩,
        ⟨9982, false, false, [], []⟩,
        ⟨9982, false, false, [], []⟩,
        ⟨9982, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [78921], .contexts [
        ⟨10071, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9979, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [78927], [9, 1, 5]⟩,
        ⟨9980, false, false, [], [9, 1, 5]⟩,
        ⟨9980, false, false, [], [9, 1, 5]⟩,
        ⟨9980, false, false, [], [9, 1, 5]⟩,
        ⟨9977, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [78925], [1, 5]⟩,
        ⟨9978, false, false, [], [1, 5]⟩,
        ⟨9978, false, false, [], [1, 5]⟩,
        ⟨9978, false, false, [], [1, 5]⟩,
        ⟨9975, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [78923], [5]⟩,
        ⟨9976, false, false, [], [5]⟩,
        ⟨9976, false, false, [], [5]⟩,
        ⟨9976, false, false, [], [5]⟩,
        ⟨9973, false, false, [], [5]⟩,
        ⟨49, false, false, [78921], []⟩,
        ⟨9974, false, false, [], []⟩,
        ⟨9974, false, false, [], []⟩,
        ⟨9974, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [78913], .contexts [
        ⟨10072, false, false, [], [3, 1, 15, 13]⟩,
        ⟨9971, false, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [78919], [1, 15, 13]⟩,
        ⟨9972, false, false, [], [1, 15, 13]⟩,
        ⟨9972, false, false, [], [1, 15, 13]⟩,
        ⟨9972, false, false, [], [1, 15, 13]⟩,
        ⟨9969, false, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [78917], [15, 13]⟩,
        ⟨9970, false, false, [], [15, 13]⟩,
        ⟨9970, false, false, [], [15, 13]⟩,
        ⟨9970, false, false, [], [15, 13]⟩,
        ⟨9967, false, false, [], [15, 13]⟩,
        ⟨3, false, false, [78915], [13]⟩,
        ⟨9968, false, false, [], [13]⟩,
        ⟨9968, false, false, [], [13]⟩,
        ⟨9968, false, false, [], [13]⟩,
        ⟨9965, false, false, [], [13]⟩,
        ⟨98, false, false, [78913], []⟩,
        ⟨9966, false, false, [], []⟩,
        ⟨9966, false, false, [], []⟩,
        ⟨9966, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [78905], .contexts [
        ⟨10073, false, false, [], [1, 11, 9, 1]⟩,
        ⟨9963, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [78911], [11, 9, 1]⟩,
        ⟨9964, false, false, [], [11, 9, 1]⟩,
        ⟨9964, false, false, [], [11, 9, 1]⟩,
        ⟨9964, false, false, [], [11, 9, 1]⟩,
        ⟨9961, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [78909], [9, 1]⟩,
        ⟨9962, false, false, [], [9, 1]⟩,
        ⟨9962, false, false, [], [9, 1]⟩,
        ⟨9962, false, false, [], [9, 1]⟩,
        ⟨9959, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [78907], [1]⟩,
        ⟨9960, false, false, [], [1]⟩,
        ⟨9960, false, false, [], [1]⟩,
        ⟨9960, false, false, [], [1]⟩,
        ⟨9957, false, false, [], [1]⟩,
        ⟨18, false, false, [78905], []⟩,
        ⟨9958, false, false, [], []⟩,
        ⟨9958, false, false, [], []⟩,
        ⟨9958, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15
    ], [78897], .contexts [
        ⟨10074, false, false, [], [5, 3, 1, 15]⟩,
        ⟨9955, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [78903], [3, 1, 15]⟩,
        ⟨9956, false, false, [], [3, 1, 15]⟩,
        ⟨9956, false, false, [], [3, 1, 15]⟩,
        ⟨9956, false, false, [], [3, 1, 15]⟩,
        ⟨9953, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [78901], [1, 15]⟩,
        ⟨9954, false, false, [], [1, 15]⟩,
        ⟨9954, false, false, [], [1, 15]⟩,
        ⟨9954, false, false, [], [1, 15]⟩,
        ⟨9951, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [78899], [15]⟩,
        ⟨9952, false, false, [], [15]⟩,
        ⟨9952, false, false, [], [15]⟩,
        ⟨9952, false, false, [], [15]⟩,
        ⟨9949, false, false, [], [15]⟩,
        ⟨3, false, false, [78897], []⟩,
        ⟨9950, false, false, [], []⟩,
        ⟨9950, false, false, [], []⟩,
        ⟨9950, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [78889], .contexts [
        ⟨10075, false, false, [], [13, 1, 11, 9]⟩,
        ⟨9947, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [78895], [1, 11, 9]⟩,
        ⟨9948, false, false, [], [1, 11, 9]⟩,
        ⟨9948, false, false, [], [1, 11, 9]⟩,
        ⟨9948, false, false, [], [1, 11, 9]⟩,
        ⟨9945, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78893], [11, 9]⟩,
        ⟨9946, false, false, [], [11, 9]⟩,
        ⟨9946, false, false, [], [11, 9]⟩,
        ⟨9946, false, false, [], [11, 9]⟩,
        ⟨9943, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [78891], [9]⟩,
        ⟨9944, false, false, [], [9]⟩,
        ⟨9944, false, false, [], [9]⟩,
        ⟨9944, false, false, [], [9]⟩,
        ⟨9941, false, false, [], [9]⟩,
        ⟨76, false, false, [78889], []⟩,
        ⟨9942, false, false, [], []⟩,
        ⟨9942, false, false, [], []⟩,
        ⟨9942, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [78881], .contexts [
        ⟨10076, false, false, [], [1, 5, 3, 1]⟩,
        ⟨9939, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78887], [5, 3, 1]⟩,
        ⟨9940, false, false, [], [5, 3, 1]⟩,
        ⟨9940, false, false, [], [5, 3, 1]⟩,
        ⟨9940, false, false, [], [5, 3, 1]⟩,
        ⟨9937, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78885], [3, 1]⟩,
        ⟨9938, false, false, [], [3, 1]⟩,
        ⟨9938, false, false, [], [3, 1]⟩,
        ⟨9938, false, false, [], [3, 1]⟩,
        ⟨9935, false, false, [], [3, 1]⟩,
        ⟨35, false, false, [78883], [1]⟩,
        ⟨9936, false, false, [], [1]⟩,
        ⟨9936, false, false, [], [1]⟩,
        ⟨9936, false, false, [], [1]⟩,
        ⟨9933, false, false, [], [1]⟩,
        ⟨18, false, false, [78881], []⟩,
        ⟨9934, false, false, [], []⟩,
        ⟨9934, false, false, [], []⟩,
        ⟨9934, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [78873], .contexts [
        ⟨10077, false, false, [], [15, 13, 1, 11]⟩,
        ⟨9931, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [78879], [13, 1, 11]⟩,
        ⟨9932, false, false, [], [13, 1, 11]⟩,
        ⟨9932, false, false, [], [13, 1, 11]⟩,
        ⟨9932, false, false, [], [13, 1, 11]⟩,
        ⟨9929, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78877], [1, 11]⟩,
        ⟨9930, false, false, [], [1, 11]⟩,
        ⟨9930, false, false, [], [1, 11]⟩,
        ⟨9930, false, false, [], [1, 11]⟩,
        ⟨9927, false, false, [], [1, 11]⟩,
        ⟨18, false, false, [78875], [11]⟩,
        ⟨9928, false, false, [], [11]⟩,
        ⟨9928, false, false, [], [11]⟩,
        ⟨9928, false, false, [], [11]⟩,
        ⟨9925, false, false, [], [11]⟩,
        ⟨90, false, false, [78873], []⟩,
        ⟨9926, false, false, [], []⟩,
        ⟨9926, false, false, [], []⟩,
        ⟨9926, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [78865], .contexts [
        ⟨10078, false, false, [], [9, 1, 5, 3]⟩,
        ⟨9923, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [78871], [1, 5, 3]⟩,
        ⟨9924, false, false, [], [1, 5, 3]⟩,
        ⟨9924, false, false, [], [1, 5, 3]⟩,
        ⟨9924, false, false, [], [1, 5, 3]⟩,
        ⟨9922, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [78869], [5, 3]⟩,
        ⟨9921, false, false, [], [5, 3]⟩,
        ⟨9921, false, false, [], [5, 3]⟩,
        ⟨9921, false, false, [], [5, 3]⟩,
        ⟨9919, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [78867], [3]⟩,
        ⟨9920, false, false, [], [3]⟩,
        ⟨9920, false, false, [], [3]⟩,
        ⟨9920, false, false, [], [3]⟩,
        ⟨9918, false, false, [], [3]⟩,
        ⟨35, false, false, [78865], []⟩,
        ⟨9917, false, false, [], []⟩,
        ⟨9917, false, false, [], []⟩,
        ⟨9917, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [78857], .contexts [
        ⟨10079, false, false, [], [1, 15, 13, 1]⟩,
        ⟨9916, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [78863], [15, 13, 1]⟩,
        ⟨9915, false, false, [], [15, 13, 1]⟩,
        ⟨9915, false, false, [], [15, 13, 1]⟩,
        ⟨9915, false, false, [], [15, 13, 1]⟩,
        ⟨9914, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [78861], [13, 1]⟩,
        ⟨9913, false, false, [], [13, 1]⟩,
        ⟨9913, false, false, [], [13, 1]⟩,
        ⟨9913, false, false, [], [13, 1]⟩,
        ⟨9912, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [78859], [1]⟩,
        ⟨9911, false, false, [], [1]⟩,
        ⟨9911, false, false, [], [1]⟩,
        ⟨9911, false, false, [], [1]⟩,
        ⟨9910, false, false, [], [1]⟩,
        ⟨18, false, false, [78857], []⟩,
        ⟨9909, false, false, [], []⟩,
        ⟨9909, false, false, [], []⟩,
        ⟨9909, false, false, [], []⟩
      ]⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [2427, 78851], .contexts [
        ⟨10080, false, false, [], [11, 9, 1, 5]⟩,
        ⟨9908, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [78855], [9, 1, 5]⟩,
        ⟨9907, false, false, [], [9, 1, 5]⟩,
        ⟨9907, false, false, [], [9, 1, 5]⟩,
        ⟨9907, false, false, [], [9, 1, 5]⟩,
        ⟨9906, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [78853], [1, 5]⟩,
        ⟨9905, false, false, [], [1, 5]⟩,
        ⟨9904, false, false, [], [1, 5]⟩,
        ⟨9905, false, false, [], [1, 5]⟩,
        ⟨9905, false, false, [], [1, 5]⟩,
        ⟨9903, true, false, [], [1, 5]⟩,
        ⟨18, false, false, [78851], [5]⟩,
        ⟨9893, false, false, [], [5]⟩,
        ⟨9892, false, false, [], [5]⟩,
        ⟨9893, false, false, [], [5]⟩,
        ⟨9893, false, false, [], [5]⟩,
        ⟨9900, false, false, [], []⟩,
        ⟨24, true, false, [], [2427, 78851]⟩,
        ⟨9897, false, false, [], []⟩,
        ⟨9898, false, false, [], []⟩,
        ⟨9898, false, false, [], []⟩
      ]⟩,
    ⟨[2429], [2427, 2423], .source 1279⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [2429, 78281], .contexts [
        ⟨10081, false, false, [], [3, 1, 15, 13]⟩,
        ⟨9890, true, false, [2427], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [2427, 78849], [1, 15, 13]⟩,
        ⟨9876, false, false, [2427], [1, 15, 13]⟩,
        ⟨9875, false, false, [2427], [15, 13]⟩,
        ⟨9872, false, false, [2427], [13]⟩,
        ⟨10082, true, false, [], [78847, 13]⟩,
        ⟨9856, true, false, [2429], [13]⟩,
        ⟨98, false, false, [2429, 78281], []⟩,
        ⟨6874, false, false, [2429], []⟩
      ]⟩,
    ⟨[2431], [2429, 275], .source 1280⟩,
    ⟨[2433], [2431, 283], .source 1281⟩,
    ⟨[2435], [2433, 1755], .source 1282⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [2435, 78719], .contexts [
        ⟨10083, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨6873, false, false, [2429], [11, 9, 1, 5]⟩,
        ⟨6870, false, false, [2429], [9, 1, 5]⟩,
        ⟨10084, true, false, [], [77261, 9, 1, 5]⟩,
        ⟨1758, false, false, [2431], [1, 5]⟩,
        ⟨10085, true, false, [], [77261, 1, 5]⟩,
        ⟨1211, false, false, [2433], [5]⟩,
        ⟨9170, false, false, [2433], []⟩,
        ⟨10086, true, false, [], [78719]⟩
      ]⟩,
    ⟨[2437], [2435, 1887], .source 1283⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [2437, 1995, 78845], .contexts [
        ⟨10087, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨9143, false, false, [2435], [1, 15, 13, 1]⟩,
        ⟨9101, false, false, [2435], [15, 13, 1]⟩,
        ⟨8068, false, false, [2435], [13, 1]⟩,
        ⟨10088, true, false, [], [78521, 13, 1]⟩,
        ⟨9766, false, false, [2437], [1]⟩,
        ⟨9768, true, false, [2437], [1]⟩,
        ⟨387, false, false, [2437, 78521], []⟩,
        ⟨390, false, false, [2437, 78521], []⟩,
        ⟨8123, false, false, [2437], [13, 1, 13]⟩,
        ⟨8410, false, false, [2437], [1, 13]⟩,
        ⟨8411, false, false, [2437], [1, 13]⟩,
        ⟨8412, false, false, [2437], [1, 13]⟩,
        ⟨8414, false, false, [2437], [1, 13]⟩,
        ⟨8093, true, false, [2437, 1993, 1898], [1, 13]⟩,
        ⟨18, false, false, [2437, 1993, 1898, 78521], [13]⟩,
        ⟨8094, true, false, [2437, 1993], [78521, 13]⟩,
        ⟨8415, true, false, [2437], [78521, 13]⟩,
        ⟨9766, false, false, [2437, 1995], []⟩,
        ⟨9769, false, false, [2437, 1995], []⟩,
        ⟨24, true, false, [2437], [1995, 78845]⟩
      ]⟩,
    ⟨[2439], [2437, 1995], .source 1284⟩,
    ⟨[2441], [2439, 1899], .source 1285⟩,
    ⟨[2443], [2441, 1251], .source 1286⟩,
    ⟨[2445], [2443, 1261], .source 1287⟩,
    ⟨[
      78983, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [2445, 1781, 78417], .contexts [
        ⟨10089, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨10090, true, false, [], [78845, 11, 9, 1, 5, 3]⟩,
        ⟨9773, false, false, [2439], [9, 1, 5, 3]⟩,
        ⟨10091, true, false, [], [77693, 9, 1, 5, 3]⟩,
        ⟨5563, false, false, [2441], [1, 5, 3]⟩,
        ⟨10092, true, false, [], [77693, 1, 5, 3]⟩,
        ⟨4123, false, false, [2443], [5, 3]⟩,
        ⟨5560, false, false, [2443, 849], [5, 3]⟩,
        ⟨5574, true, false, [2443], [77693, 5, 3]⟩,
        ⟨10093, true, false, [], [77693, 5, 3]⟩,
        ⟨7685, false, false, [2445], [3]⟩,
        ⟨7703, false, false, [2445], []⟩
      ]⟩,
    ⟨[2447], [2445, 1781], .source 1288⟩,
    ⟨[2449], [2447, 1261], .source 1289⟩,
    ⟨[2451], [2449, 831], .source 1290⟩,
    ⟨[1, 13], [
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14
    ], .contexts [
        ⟨764, false, false, [10, 8, 0, 4, 2, 0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14
        ]⟩
      ]⟩,
    ⟨[
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨967, false, false, [], [
          0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
          0
        ]⟩,
        ⟨19, false, false, [11, 9], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [11, 9, 1], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [11, 9, 1, 5], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [11, 9, 1, 5, 3], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [11, 9, 1, 5, 3, 1], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [11, 9, 1, 5, 3, 1, 15], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [11, 9, 1, 5, 3, 1, 15, 13], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [11, 9, 1, 5, 3, 1, 15, 13, 1], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [4, 2, 0]⟩,
        ⟨50, false, false, [11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [2, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5
        ], [0]⟩
      ]⟩,
    ⟨[
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨10099, false, false, [], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩,
    ⟨[
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨10100, false, false, [], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11
        ], [0]⟩
      ]⟩,
    ⟨[
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨10101, false, false, [], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5
        ], [0]⟩
      ]⟩,
    ⟨[
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 0
    ], .contexts [
        ⟨10102, false, false, [], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15
        ], [0]⟩
      ]⟩,
    ⟨[
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 0
    ], .contexts [
        ⟨10103, false, false, [], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0]⟩,
        ⟨77, false, false, [
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
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 0
    ], .contexts [
        ⟨10104, false, false, [], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨108, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0]⟩,
        ⟨91, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0]⟩,
        ⟨77, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0]⟩,
        ⟨50, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0]⟩,
        ⟨36, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
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
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
      14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
      10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
      4, 2, 0, 14
    ], [
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], .contexts [
        ⟨10105, false, false, [], [14]⟩,
        ⟨19, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3
        ], [14]⟩,
        ⟨20, false, false, [
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
          15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
          11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
          5, 3, 1
        ], []⟩
      ]⟩,
    ⟨[78985, 13], [78985, 13], .contexts []⟩,
    ⟨[78985, 13], [2451, 78417], .contexts [
        ⟨10107, false, false, [], []⟩,
        ⟨10053, true, false, [], [13]⟩,
        ⟨10053, true, false, [], [13]⟩,
        ⟨10051, true, false, [], [13]⟩,
        ⟨10098, false, false, [78983], []⟩,
        ⟨10106, false, false, [78983], []⟩,
        ⟨10094, false, false, [], [1, 15]⟩,
        ⟨10095, true, false, [], [78417, 1, 15]⟩,
        ⟨7693, false, false, [2447], [15]⟩,
        ⟨10096, true, false, [], [78417, 15]⟩,
        ⟨7688, true, false, [2449], [15]⟩,
        ⟨290, false, false, [2449, 77693], []⟩,
        ⟨291, false, false, [2449, 77693], []⟩,
        ⟨3870, false, false, [2449], [5]⟩,
        ⟨5551, false, false, [2449], [5]⟩,
        ⟨4120, false, false, [2449], [5]⟩,
        ⟨4120, false, false, [2449], [5]⟩,
        ⟨7685, false, false, [2449, 831], []⟩,
        ⟨7692, false, false, [2449, 831], []⟩,
        ⟨4032, true, false, [2449], [78417]⟩,
        ⟨10097, true, false, [], [78417]⟩
      ]⟩,
    ⟨[78985, 13], [2451, 78417], .contexts [
        ⟨10108, false, false, [], []⟩,
        ⟨7692, false, false, [2451], []⟩,
        ⟨24, true, false, [], [2451, 78417]⟩
      ]⟩,
    ⟨[2453], [2450], .source 1291⟩,
    ⟨[2451, 78417], [2451, 78417], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 158. -/
def y322TCContextRaw158 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78985, 13], [2451, 78417], .contexts [
        ⟨10107, false, false, [], []⟩,
        ⟨10109, false, false, [], []⟩,
        ⟨10111, false, false, [], []⟩,
        ⟨10111, false, false, [], []⟩
      ]⟩,
    ⟨[78985], [78985], .contexts []⟩,
    ⟨[78985], [78985], .contexts []⟩,
    ⟨[2465], [2451, 1295], .source 1297⟩,
    ⟨[77585, 5], [77585, 5], .contexts []⟩,
    ⟨[2467], [2464], .source 1298⟩,
    ⟨[2464], [2464], .contexts []⟩,
    ⟨[77585, 5], [2467, 78985], .contexts [
        ⟨10116, false, false, [], []⟩,
        ⟨10115, false, false, [2464], [77585, 5]⟩,
        ⟨5706, true, false, [2464, 2451], [5]⟩,
        ⟨3868, true, false, [2464, 2451], [5]⟩,
        ⟨7686, true, false, [2464, 2451], [13, 5]⟩,
        ⟨10112, true, false, [2464], [5, 13, 5]⟩,
        ⟨1846, false, false, [2464, 78985], []⟩,
        ⟨10113, false, false, [2464], []⟩,
        ⟨10114, false, false, [2464], []⟩,
        ⟨10118, true, false, [], [78985]⟩,
        ⟨10118, true, false, [], [78985]⟩,
        ⟨10117, true, false, [], [78985]⟩
      ]⟩,
    ⟨[2469], [2451, 1251], .source 1299⟩,
    ⟨[2471], [2469, 2453], .source 1300⟩,
    ⟨[13, 9, 13, 9], [], .contexts [
        ⟨129, false, false, [], []⟩
      ]⟩,
    ⟨[2473], [2470], .source 1301⟩,
    ⟨[2470], [2470], .contexts []⟩,
    ⟨[78421, 11], [78421, 11], .contexts []⟩,
    ⟨[2450], [2450], .contexts []⟩,
    ⟨[78421, 11], [2453, 78985], .contexts [
        ⟨10125, false, false, [], []⟩,
        ⟨7715, true, false, [], [11]⟩,
        ⟨7706, true, false, [], [13, 11]⟩,
        ⟨10112, true, false, [2450], [11, 13, 11]⟩,
        ⟨9287, false, false, [2450, 78985], []⟩,
        ⟨10113, false, false, [2450], []⟩,
        ⟨10114, false, false, [2450], []⟩,
        ⟨10126, true, false, [], [78985]⟩,
        ⟨10126, true, false, [], [78985]⟩,
        ⟨10110, true, false, [], [78985]⟩
      ]⟩,
    ⟨[2467, 78985], [2467, 78985], .contexts []⟩,
    ⟨[2467, 78985], [2467, 78985], .contexts []⟩,
    ⟨[77585, 5], [2467, 78985], .contexts [
        ⟨10116, false, false, [], []⟩,
        ⟨10119, false, false, [], []⟩,
        ⟨10128, false, false, [], []⟩,
        ⟨10129, false, false, [], []⟩,
        ⟨10129, false, false, [], []⟩
      ]⟩,
    ⟨[2465], [2466], .contexts [
        ⟨10117, true, true, [], []⟩
      ]⟩,
    ⟨[2466], [2466], .contexts []⟩,
    ⟨[78983, 5], [2465, 77583], .contexts [
        ⟨10052, true, false, [], [5]⟩,
        ⟨10130, true, false, [2466], [1, 5]⟩,
        ⟨1509, false, false, [2466, 77585], []⟩,
        ⟨19, false, false, [2466, 77585], []⟩,
        ⟨3165, false, false, [2466], []⟩,
        ⟨3166, false, false, [2466], []⟩,
        ⟨3120, false, false, [2466], []⟩,
        ⟨3120, false, false, [2466], []⟩,
        ⟨3468, false, false, [2466], []⟩,
        ⟨10132, true, false, [], [77583]⟩,
        ⟨10132, true, false, [], [77583]⟩,
        ⟨10131, true, false, [], [77583]⟩
      ]⟩,
    ⟨[1851, 78531], [1851, 78531], .contexts []⟩,
    ⟨[1851, 78531], [1851, 78531], .contexts []⟩,
    ⟨[2477], [1851, 1857], .source 1303⟩,
    ⟨[2479], [2465, 2477], .source 1304⟩,
    ⟨[2453, 78985], [2453, 78985], .contexts []⟩,
    ⟨[2453, 78981], [2453, 78981], .contexts []⟩,
    ⟨[2452], [2452], .contexts []⟩,
    ⟨[78981, 1], [2451, 78421], .contexts [
        ⟨10139, true, false, [2452], [1]⟩,
        ⟨10049, true, false, [], [1]⟩,
        ⟨10052, true, false, [], [11, 1]⟩,
        ⟨10138, true, false, [2452], [1, 11, 1]⟩,
        ⟨10138, true, false, [2452], [1, 11, 1]⟩,
        ⟨10127, true, false, [2452], [1, 11, 1]⟩,
        ⟨10125, true, false, [2452], [1, 11, 1]⟩,
        ⟨1068, false, false, [2452, 78421], []⟩,
        ⟨7723, false, false, [2452], []⟩,
        ⟨10140, true, false, [], [78421]⟩,
        ⟨10140, true, false, [], [78421]⟩,
        ⟨10110, false, true, [], [78421]⟩
      ]⟩,
    ⟨[1901, 78555], [1901, 78555], .contexts []⟩,
    ⟨[2483], [1899, 2453], .source 1306⟩,
    ⟨[2485], [2482], .source 1307⟩,
    ⟨[78981], [2485, 78555], .contexts [
        ⟨10143, false, false, [2482], [78981]⟩,
        ⟨8140, false, false, [2482], [2453, 78981]⟩,
        ⟨10139, true, false, [2482, 1900], []⟩,
        ⟨10110, false, false, [2482, 1900], [78981]⟩,
        ⟨18, true, false, [2482, 1900, 2450, 78981], []⟩,
        ⟨10141, false, false, [2482, 1900, 2450], [1]⟩,
        ⟨9784, true, false, [2482, 1900, 1898], [1]⟩,
        ⟨8393, false, false, [2482, 1900, 1898], []⟩,
        ⟨8395, false, false, [2482, 1900, 1898], []⟩,
        ⟨9785, true, false, [2482, 1900], [78555]⟩,
        ⟨10142, false, false, [2482, 1900], []⟩,
        ⟨10142, false, false, [2482, 1900], []⟩,
        ⟨10144, true, false, [], [78555]⟩
      ]⟩,
    ⟨[2483], [2484], .contexts [
        ⟨10144, true, true, [], []⟩
      ]⟩,
    ⟨[2484], [2484], .contexts []⟩,
    ⟨[78555, 11], [2483, 78983], .contexts [
        ⟨10145, true, false, [2484], [11]⟩,
        ⟨10047, false, false, [2484], []⟩,
        ⟨10147, true, false, [], [78983]⟩,
        ⟨10147, true, false, [], [78983]⟩,
        ⟨10146, true, false, [], [78983]⟩
      ]⟩,
    ⟨[2485, 78557], [2485, 78557], .contexts []⟩,
    ⟨[2487], [2485, 1899], .source 1308⟩,
    ⟨[2487, 77681], [78977], .contexts [
        ⟨10150, false, false, [], [77681]⟩,
        ⟨8444, true, false, [2485], []⟩,
        ⟨10149, true, false, [], [1]⟩,
        ⟨10144, false, false, [], [78557, 1]⟩,
        ⟨10149, true, false, [2482, 2484], [1]⟩,
        ⟨8423, true, false, [2482], [1]⟩,
        ⟨10145, true, false, [2482, 2484], [9, 1]⟩,
        ⟨10045, false, false, [2482, 2484], [1]⟩,
        ⟨10054, false, false, [2482, 2484], [1]⟩,
        ⟨24, true, false, [2482, 2484], [78979, 1]⟩,
        ⟨10146, true, false, [2482], [78979, 1]⟩,
        ⟨10042, false, false, [], []⟩
      ]⟩,
    ⟨[2489], [2486], .source 1309⟩,
    ⟨[2489], [2486], .contexts [
        ⟨10152, false, false, [], []⟩,
        ⟨24, false, false, [2486], []⟩
      ]⟩,
    ⟨[2487], [2488], .contexts [
        ⟨10152, true, true, [], []⟩
      ]⟩,
    ⟨[2487, 77683], [2487, 77683], .contexts []⟩,
    ⟨[78975, 3], [2487, 1773, 77683], .contexts [
        ⟨10153, false, false, [2488], [78975, 3]⟩,
        ⟨10056, true, false, [2488, 2486], [3]⟩,
        ⟨10039, true, false, [2488, 2486], [3]⟩,
        ⟨10153, false, false, [2488, 2486, 2488], [78977, 5, 3]⟩,
        ⟨10055, true, false, [2488, 2486, 2488, 2486], [5, 3]⟩,
        ⟨10151, true, false, [2488, 2486, 2488, 2486], [5, 3]⟩,
        ⟨10154, true, false, [2488, 2486], [77681, 5, 3]⟩,
        ⟨3850, false, false, [2488], [3]⟩,
        ⟨10155, false, false, [2488, 2486], [3]⟩,
        ⟨10154, true, false, [], [77683, 3]⟩,
        ⟨10155, false, false, [], [3]⟩,
        ⟨7596, false, false, [2487], []⟩
      ]⟩,
    ⟨[2491], [2487, 1773], .source 1310⟩,
    ⟨[2493], [2490], .source 1311⟩,
    ⟨[2493], [2490], .contexts [
        ⟨10158, false, false, [], []⟩,
        ⟨24, false, false, [2490], []⟩
      ]⟩,
    ⟨[2491], [2492], .contexts [
        ⟨10158, true, true, [], []⟩
      ]⟩,
    ⟨[2491, 77685], [2491, 77685], .contexts []⟩,
    ⟨[78971], [2492, 77685], .contexts [
        ⟨10159, false, false, [2492], [78971]⟩,
        ⟨10059, true, false, [2492, 2490], []⟩,
        ⟨10033, true, false, [2492, 2490], []⟩,
        ⟨10159, false, false, [2492, 2490, 2492], [78973, 1]⟩,
        ⟨10057, true, false, [2492, 2490, 2492, 2490], [1]⟩,
        ⟨10036, true, false, [2492, 2490, 2492, 2490], [1]⟩,
        ⟨10156, false, false, [2492, 2490, 2492, 2490], [1]⟩,
        ⟨10157, true, false, [2492, 2490, 2492, 2490], [77683, 1]⟩,
        ⟨10160, true, false, [2492, 2490], [77683, 1]⟩,
        ⟨3854, false, false, [2492], []⟩,
        ⟨10161, false, false, [2492, 2490], []⟩
      ]⟩,
    ⟨[2495], [2491, 2189], .source 1312⟩,
    ⟨[2497], [2494], .source 1313⟩,
    ⟨[2499], [2495, 2191], .source 1314⟩,
    ⟨[78969, 13], [2499, 77573], .contexts [
        ⟨10164, false, false, [2496], [78969, 13]⟩,
        ⟨24, false, false, [2496, 2494], [78969, 13]⟩,
        ⟨10060, true, false, [2496, 2494], [13]⟩,
        ⟨10030, true, false, [2496, 2494], [13]⟩,
        ⟨10162, false, false, [2496, 2494], [15, 13]⟩,
        ⟨10160, true, false, [2496, 2494], [77685, 15, 13]⟩,
        ⟨10161, false, false, [2496, 2494], [15, 13]⟩,
        ⟨9655, true, false, [2496, 2494, 2491, 2186], [15, 13]⟩,
        ⟨3, false, false, [2496, 2494, 2491, 2186, 78825], [13]⟩,
        ⟨9125, true, false, [2496, 2494, 2491], [78825, 13]⟩,
        ⟨10163, true, false, [2496, 2494], [78825, 13]⟩,
        ⟨10164, false, true, [], [78825, 13]⟩,
        ⟨9651, false, false, [2495], []⟩,
        ⟨10165, true, false, [], [77573]⟩
      ]⟩,
    ⟨[2501], [2498], .source 1315⟩,
    ⟨[2501], [2498], .contexts [
        ⟨10167, false, false, [], []⟩
      ]⟩,
    ⟨[2501], [2498], .contexts [
        ⟨10168, false, false, [], []⟩,
        ⟨24, false, false, [2498], []⟩
      ]⟩,
    ⟨[2499], [2500], .contexts [
        ⟨10167, true, true, [], []⟩
      ]⟩,
    ⟨[2499, 77571, 11], [78963], .contexts [
        ⟨10170, false, false, [], [77571, 11]⟩,
        ⟨3099, true, false, [2500], [11]⟩,
        ⟨10170, false, false, [2500, 2498], [77573, 1, 11]⟩,
        ⟨10166, true, false, [2500, 2498, 2500, 2498], [1, 11]⟩,
        ⟨10027, false, false, [2500, 2498, 2500, 2498], [1, 11]⟩,
        ⟨10061, false, false, [2500, 2498, 2500, 2498], [1, 11]⟩,
        ⟨10169, true, false, [2500, 2498, 2500], [78967, 1, 11]⟩,
        ⟨10024, false, false, [2500, 2498], [11]⟩,
        ⟨10062, false, false, [2500, 2498], [11]⟩,
        ⟨10169, true, false, [2500], [78965, 11]⟩,
        ⟨10021, false, false, [], []⟩
      ]⟩,
    ⟨[2498], [2498], .contexts []⟩,
    ⟨[77571, 11], [2501, 78963], .contexts [
        ⟨10171, false, false, [2498], []⟩,
        ⟨10063, false, false, [2498], []⟩,
        ⟨10172, true, false, [], [78963]⟩,
        ⟨10172, true, false, [], [78963]⟩,
        ⟨10168, true, false, [], [78963]⟩
      ]⟩,
    ⟨[2501, 78963], [2501, 78963], .contexts []⟩,
    ⟨[2501, 78963], [2501, 78963], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 159. -/
def y322TCContextRaw159 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2509], [1893, 2501], .source 1319⟩,
    ⟨[78961, 11], [78961, 11], .contexts []⟩,
    ⟨[78961], [78961], .contexts []⟩,
    ⟨[2511], [2508], .source 1320⟩,
    ⟨[2513], [2511, 2501], .source 1321⟩,
    ⟨[2513, 78961], [2513, 78961], .contexts []⟩,
    ⟨[78961, 11], [2513, 78961], .contexts [
        ⟨10177, false, false, [], []⟩,
        ⟨10177, false, false, [], []⟩,
        ⟨10018, true, false, [], [11]⟩,
        ⟨10176, false, false, [2508], [78963, 9, 11]⟩,
        ⟨10173, true, false, [2508, 1893], [9, 11]⟩,
        ⟨8176, true, false, [2508], [11, 9, 11]⟩,
        ⟨966, false, false, [2508, 77571], []⟩,
        ⟨967, false, false, [2508, 77571], []⟩,
        ⟨10173, false, false, [2508], [9]⟩,
        ⟨10174, false, false, [2508], [9]⟩,
        ⟨10175, false, false, [2508], [9]⟩,
        ⟨10175, false, false, [2508], [9]⟩,
        ⟨10018, false, false, [2508, 2501], []⟩,
        ⟨10178, false, false, [2508, 2501], []⟩,
        ⟨10179, true, false, [], [2501, 78961]⟩,
        ⟨10180, true, false, [], [78961]⟩,
        ⟨10181, false, false, [], []⟩,
        ⟨10181, false, false, [], []⟩
      ]⟩,
    ⟨[78961, 1], [78959], .contexts [
        ⟨10066, false, false, [], []⟩,
        ⟨10067, false, false, [], []⟩,
        ⟨10013, false, false, [], []⟩,
        ⟨10013, false, false, [], []⟩
      ]⟩,
    ⟨[78959], [78959], .contexts []⟩,
    ⟨[2517], [2512], .source 1323⟩,
    ⟨[2512], [2512], .contexts []⟩,
    ⟨[78987], [77141, 7], .source 39558⟩,
    ⟨[77141, 7], [78987], .contexts [
        ⟨10187, true, false, [], []⟩
      ]⟩,
    ⟨[78987], [78987], .contexts []⟩,
    ⟨[77141, 1], [77139], .contexts [
        ⟨711, false, false, [], []⟩,
        ⟨712, false, false, [], []⟩,
        ⟨460, false, false, [], []⟩,
        ⟨460, false, false, [], []⟩
      ]⟩,
    ⟨[78987, 1], [78987, 1], .contexts []⟩,
    ⟨[78989], [77143, 1], .source 39559⟩,
    ⟨[77143, 1], [78989], .contexts [
        ⟨10192, true, false, [], []⟩
      ]⟩,
    ⟨[78989, 1], [77143], .contexts [
        ⟨10193, true, false, [], [1]⟩,
        ⟨18, false, false, [77143], []⟩,
        ⟨467, false, false, [], []⟩
      ]⟩,
    ⟨[78989], [78989], .contexts []⟩,
    ⟨[78989], [78989], .contexts []⟩,
    ⟨[77143, 1], [78989], .contexts [
        ⟨10193, false, false, [], []⟩,
        ⟨10195, false, false, [], []⟩,
        ⟨10196, false, false, [], []⟩,
        ⟨10196, false, false, [], []⟩
      ]⟩,
    ⟨[77143, 5], [78825], .contexts [
        ⟨9644, false, false, [], []⟩,
        ⟨9637, false, false, [], []⟩,
        ⟨9638, false, false, [], []⟩,
        ⟨9638, false, false, [], []⟩
      ]⟩,
    ⟨[78989, 5], [78989, 5], .contexts []⟩,
    ⟨[78827], [78827], .contexts [
        ⟨9680, false, false, [], []⟩
      ]⟩,
    ⟨[78827], [78827], .contexts [
        ⟨1118, true, false, [], [78827]⟩
      ]⟩,
    ⟨[78989, 5], [78827], .contexts [
        ⟨10199, false, false, [], []⟩,
        ⟨10197, true, false, [], [5]⟩,
        ⟨165, false, false, [77143], []⟩,
        ⟨166, false, false, [77143], []⟩,
        ⟨10198, false, false, [], [1]⟩,
        ⟨9658, false, false, [], []⟩,
        ⟨9659, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨10200, false, false, [], []⟩,
        ⟨10201, false, false, [], []⟩
      ]⟩,
    ⟨[77143, 11], [77145], .contexts [
        ⟨466, false, false, [], []⟩
      ]⟩,
    ⟨[77145, 1], [77147], .contexts [
        ⟨469, false, false, [], []⟩
      ]⟩,
    ⟨[78989, 11], [78989, 11], .contexts []⟩,
    ⟨[77147], [77147], .contexts [
        ⟨8473, false, false, [], []⟩
      ]⟩,
    ⟨[77147], [77147], .contexts [
        ⟨1118, true, false, [], [77147]⟩
      ]⟩,
    ⟨[78989, 11], [77147], .contexts [
        ⟨10205, false, false, [], []⟩,
        ⟨10197, true, false, [], [11]⟩,
        ⟨181, false, false, [77143], []⟩,
        ⟨182, false, false, [77143], []⟩,
        ⟨10203, false, false, [], [1]⟩,
        ⟨706, false, false, [], [1]⟩,
        ⟨470, false, false, [], [1]⟩,
        ⟨470, false, false, [], [1]⟩,
        ⟨10204, false, false, [], []⟩,
        ⟨704, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩,
        ⟨10206, false, false, [], []⟩,
        ⟨10207, false, false, [], []⟩
      ]⟩,
    ⟨[77147, 11], [78989], .contexts [
        ⟨10208, true, false, [], [11]⟩,
        ⟨90, false, false, [78989], []⟩,
        ⟨10196, false, false, [], []⟩
      ]⟩,
    ⟨[1887, 78557], [1887, 78557], .contexts []⟩,
    ⟨[78989, 15], [78989, 15], .contexts []⟩,
    ⟨[78991], [78989, 9], .source 39560⟩,
    ⟨[78989, 9], [78991], .contexts [
        ⟨10212, true, false, [], []⟩
      ]⟩,
    ⟨[78989, 9], [78991], .contexts [
        ⟨10213, false, false, [], []⟩
      ]⟩,
    ⟨[78991], [78991], .contexts []⟩,
    ⟨[78991], [78991], .contexts []⟩,
    ⟨[78989, 9], [78991], .contexts [
        ⟨10214, false, false, [], []⟩,
        ⟨10215, false, false, [], []⟩,
        ⟨10216, false, false, [], []⟩,
        ⟨10216, false, false, [], []⟩
      ]⟩,
    ⟨[78989, 1], [77143], .contexts [
        ⟨10194, false, false, [], []⟩,
        ⟨708, false, false, [], []⟩,
        ⟨467, false, false, [], []⟩,
        ⟨467, false, false, [], []⟩
      ]⟩,
    ⟨[78991, 1], [78835], .contexts [
        ⟨10217, true, false, [], [1]⟩,
        ⟨1143, false, false, [78989], []⟩,
        ⟨1146, false, false, [78989], []⟩,
        ⟨10218, false, false, [], [9, 1, 9]⟩,
        ⟨709, false, false, [], [1, 9]⟩,
        ⟨710, false, false, [], [1, 9]⟩,
        ⟨463, false, false, [], [1, 9]⟩,
        ⟨463, false, false, [], [1, 9]⟩,
        ⟨711, false, false, [], [9]⟩,
        ⟨712, false, false, [], [9]⟩,
        ⟨460, false, false, [], [9]⟩,
        ⟨460, false, false, [], [9]⟩,
        ⟨9728, false, false, [], []⟩,
        ⟨9729, false, false, [], []⟩,
        ⟨9730, false, false, [], []⟩,
        ⟨9730, false, false, [], []⟩,
        ⟨9735, false, false, [], []⟩,
        ⟨1118, true, false, [], [78835]⟩
      ]⟩,
    ⟨[78835, 1], [78991], .contexts [
        ⟨10219, true, false, [], [1]⟩,
        ⟨18, false, false, [78991], []⟩,
        ⟨10216, false, false, [], []⟩
      ]⟩,
    ⟨[78989, 5], [78827], .contexts [
        ⟨10199, false, false, [], []⟩,
        ⟨10202, false, false, [], []⟩,
        ⟨9659, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩
      ]⟩,
    ⟨[78989, 11], [77147], .contexts [
        ⟨10205, false, false, [], []⟩,
        ⟨10208, false, false, [], []⟩,
        ⟨704, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩
      ]⟩,
    ⟨[78991], [78991], .contexts []⟩,
    ⟨[2007], [2007], .contexts [
        ⟨24, false, false, [], [2007]⟩
      ]⟩,
    ⟨[2187, 77681], [2187, 77681], .contexts []⟩,
    ⟨[78989, 15], [2187, 77681], .contexts [
        ⟨10211, false, false, [], []⟩,
        ⟨10211, false, false, [], []⟩,
        ⟨10197, true, false, [], [15]⟩,
        ⟨199, false, false, [77143], []⟩,
        ⟨200, false, false, [77143], []⟩,
        ⟨8442, false, false, [], [1]⟩,
        ⟨10210, false, false, [], [1]⟩,
        ⟨10210, false, false, [], [1]⟩,
        ⟨8444, false, false, [1887], []⟩,
        ⟨9120, true, false, [], [77681]⟩,
        ⟨8166, false, false, [2187], []⟩,
        ⟨9124, true, false, [], [77681]⟩,
        ⟨10225, false, false, [], []⟩,
        ⟨10225, false, false, [], []⟩
      ]⟩,
    ⟨[2525], [2187, 1901], .source 1327⟩,
    ⟨[2525, 78515], [2525, 78515], .contexts [
        ⟨8173, false, false, [2525], []⟩
      ]⟩,
    ⟨[2525, 78515], [2525, 78515], .contexts [
        ⟨24, true, false, [], [2525, 78515]⟩
      ]⟩,
    ⟨[78991, 15], [2525, 78515], .contexts [
        ⟨10217, true, false, [], [15]⟩,
        ⟨323, false, false, [78989], []⟩,
        ⟨324, false, false, [78989], []⟩,
        ⟨10226, false, false, [], [9]⟩,
        ⟨8170, false, false, [2187], []⟩,
        ⟨10227, true, false, [], [78515]⟩,
        ⟨10228, false, false, [], []⟩,
        ⟨10229, false, false, [], []⟩
      ]⟩,
    ⟨[2527], [2524], .source 1328⟩,
    ⟨[78993], [77141, 11], .source 39561⟩,
    ⟨[77141, 11], [78993], .contexts [
        ⟨10232, true, false, [], []⟩
      ]⟩,
    ⟨[77141, 11], [78993], .contexts [
        ⟨10233, false, false, [], []⟩
      ]⟩,
    ⟨[78993], [78993], .contexts []⟩,
    ⟨[78993], [78993], .contexts []⟩,
    ⟨[77141, 11], [78993], .contexts [
        ⟨10234, false, false, [], []⟩,
        ⟨10235, false, false, [], []⟩,
        ⟨10236, false, false, [], []⟩,
        ⟨10236, false, false, [], []⟩
      ]⟩,
    ⟨[78993, 1], [78993, 1], .contexts []⟩,
    ⟨[78993, 1], [78837], .contexts [
        ⟨10238, false, false, [], []⟩,
        ⟨10237, true, false, [], [1]⟩,
        ⟨992, false, false, [77141], []⟩,
        ⟨993, false, false, [77141], []⟩,
        ⟨10190, false, false, [], [11]⟩,
        ⟨9742, false, false, [], []⟩,
        ⟨9743, false, false, [], []⟩,
        ⟨9744, false, false, [], []⟩,
        ⟨9744, false, false, [], []⟩,
        ⟨9746, false, false, [], []⟩,
        ⟨1118, true, false, [], [78837]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 160. -/
def y322TCContextRaw160 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77141, 5], [78717], .contexts [
        ⟨9106, true, false, [], [5]⟩,
        ⟨49, false, false, [78717], []⟩,
        ⟨9103, false, false, [], []⟩,
        ⟨9102, false, false, [], []⟩,
        ⟨9103, false, false, [], []⟩,
        ⟨9103, false, false, [], []⟩
      ]⟩,
    ⟨[78993, 5], [78993, 5], .contexts []⟩,
    ⟨[78993, 5], [2183, 77581], .contexts [
        ⟨10241, false, false, [], []⟩,
        ⟨10237, true, false, [], [5]⟩,
        ⟨1083, false, false, [77141], []⟩,
        ⟨1084, false, false, [77141], []⟩,
        ⟨10240, false, false, [], [11]⟩,
        ⟨9126, false, false, [], []⟩,
        ⟨9127, false, false, [], []⟩,
        ⟨9128, false, false, [], []⟩,
        ⟨9128, false, false, [], []⟩,
        ⟨9112, false, false, [], []⟩,
        ⟨9113, false, false, [], []⟩
      ]⟩,
    ⟨[1887, 78555], [1887, 78555], .contexts []⟩,
    ⟨[77141, 15], [1887, 78555], .contexts [
        ⟨8408, false, false, [], []⟩,
        ⟨10243, false, false, [], []⟩,
        ⟨10243, false, false, [], []⟩
      ]⟩,
    ⟨[2529], [1887, 2483], .source 1329⟩,
    ⟨[2529], [2529], .contexts []⟩,
    ⟨[2529], [2529], .contexts []⟩,
    ⟨[78995], [77141, 13], .source 39562⟩,
    ⟨[77141, 13], [78995], .contexts [
        ⟨10248, true, false, [], []⟩
      ]⟩,
    ⟨[77141, 13], [78995], .contexts [
        ⟨10249, false, false, [], []⟩
      ]⟩,
    ⟨[78995], [78995], .contexts []⟩,
    ⟨[78995], [78995], .contexts []⟩,
    ⟨[77141, 13], [78995], .contexts [
        ⟨10250, false, false, [], []⟩,
        ⟨10251, false, false, [], []⟩,
        ⟨10252, false, false, [], []⟩,
        ⟨10252, false, false, [], []⟩
      ]⟩,
    ⟨[78995], [78995], .contexts []⟩,
    ⟨[78995, 1], [1075, 78995], .contexts [
        ⟨10253, true, false, [], [1]⟩,
        ⟨387, false, false, [77141], []⟩,
        ⟨390, false, false, [77141], []⟩,
        ⟨10190, false, false, [], [13, 1, 13]⟩,
        ⟨9721, false, false, [], [1, 13]⟩,
        ⟨9722, false, false, [], [1, 13]⟩,
        ⟨9723, false, false, [], [1, 13]⟩,
        ⟨9723, false, false, [], [1, 13]⟩,
        ⟨459, false, false, [1075], [13]⟩,
        ⟨10249, false, false, [1075], []⟩,
        ⟨10254, false, false, [1075], []⟩,
        ⟨9215, true, false, [], [78995]⟩
      ]⟩,
    ⟨[78995, 5], [2191, 77575], .contexts [
        ⟨10253, true, false, [], [5]⟩,
        ⟨116, false, false, [77141], []⟩,
        ⟨117, false, false, [77141], []⟩,
        ⟨10240, false, false, [], [13]⟩,
        ⟨9645, false, false, [], []⟩,
        ⟨9135, false, false, [], []⟩,
        ⟨9136, false, false, [], []⟩,
        ⟨9136, false, false, [], []⟩,
        ⟨3528, false, false, [2191], []⟩,
        ⟨9649, true, false, [], [77575]⟩
      ]⟩,
    ⟨[2533], [1887, 1997], .source 1331⟩,
    ⟨[2535], [2533, 1885], .source 1332⟩,
    ⟨[2535, 78995], [2535, 78995], .contexts []⟩,
    ⟨[2535, 78995], [2535, 78995], .contexts []⟩,
    ⟨[2535], [2535], .contexts []⟩,
    ⟨[2535], [2535], .contexts []⟩,
    ⟨[78995, 15], [2535, 78995], .contexts [
        ⟨10253, true, false, [], [15]⟩,
        ⟨148, false, false, [77141], []⟩,
        ⟨150, false, false, [77141], []⟩,
        ⟨10244, false, false, [], [13, 15, 13]⟩,
        ⟨8421, false, false, [1887], [15, 13]⟩,
        ⟨10257, true, false, [], [78555, 15, 13]⟩,
        ⟨8407, false, false, [2533], [13]⟩,
        ⟨10258, true, false, [], [77141, 13]⟩,
        ⟨10249, false, false, [2535], []⟩,
        ⟨10259, false, false, [], []⟩,
        ⟨10260, false, false, [], []⟩,
        ⟨10254, false, false, [2535], []⟩,
        ⟨10262, true, false, [], [78995]⟩,
        ⟨10261, true, false, [], [78995]⟩,
        ⟨24, true, false, [], [2535, 78995]⟩
      ]⟩,
    ⟨[79001], [78829, 15], .source 39565⟩,
    ⟨[78829, 15], [79001], .contexts [
        ⟨10264, true, false, [], []⟩
      ]⟩,
    ⟨[79001], [79001], .contexts []⟩,
    ⟨[79001], [79001], .contexts []⟩,
    ⟨[77139, 15], [1887, 78553], .contexts [
        ⟨8391, false, false, [], []⟩
      ]⟩,
    ⟨[1887, 78553], [1887, 1899, 78421], .contexts [
        ⟨9786, false, false, [1887], []⟩
      ]⟩,
    ⟨[1887, 1899, 78421], [2187, 78421], .contexts [
        ⟨9120, true, false, [], [78421]⟩
      ]⟩,
    ⟨[2187, 78421], [2187, 78421], .contexts []⟩,
    ⟨[79001, 7], [79001, 7], .contexts []⟩,
    ⟨[2187, 78421], [2187, 78421], .contexts [
        ⟨7723, false, false, [2187], []⟩
      ]⟩,
    ⟨[2187, 78421], [2187, 78421], .contexts [
        ⟨9124, true, false, [], [78421]⟩
      ]⟩,
    ⟨[79003], [78835, 15], .source 39566⟩,
    ⟨[78835, 15], [79003], .contexts [
        ⟨10275, true, false, [], []⟩
      ]⟩,
    ⟨[79003, 15], [78835], .contexts [
        ⟨10276, true, false, [], [15]⟩,
        ⟨3, false, false, [78835], []⟩,
        ⟨9730, false, false, [], []⟩
      ]⟩,
    ⟨[79003], [79003], .contexts []⟩,
    ⟨[78835, 15], [79003], .contexts [
        ⟨10276, false, false, [], []⟩,
        ⟨10278, false, false, [], []⟩,
        ⟨10278, false, false, [], []⟩
      ]⟩,
    ⟨[2525, 78515], [2525, 78515], .contexts []⟩,
    ⟨[2525, 78515], [2525, 78515], .contexts []⟩,
    ⟨[79003, 1], [79003, 1], .contexts []⟩,
    ⟨[79003, 1], [2525, 78515], .contexts [
        ⟨10282, false, false, [], []⟩,
        ⟨10279, true, false, [], [1]⟩,
        ⟨17, false, false, [78835], []⟩,
        ⟨21, false, false, [78835], []⟩,
        ⟨10220, false, false, [], [15]⟩,
        ⟨10215, false, false, [], [15]⟩,
        ⟨10216, false, false, [], [15]⟩,
        ⟨10216, false, false, [], [15]⟩,
        ⟨10230, false, false, [], []⟩,
        ⟨10280, false, false, [], []⟩,
        ⟨10281, false, false, [], []⟩,
        ⟨10281, false, false, [], []⟩,
        ⟨10228, false, false, [], []⟩,
        ⟨10229, false, false, [], []⟩
      ]⟩,
    ⟨[78515, 1], [2527, 79003], .contexts [
        ⟨10283, true, false, [2524], [1]⟩,
        ⟨18, false, false, [2524, 79003], []⟩,
        ⟨10231, true, false, [], [79003]⟩
      ]⟩,
    ⟨[315, 79003], [315, 79003], .contexts []⟩,
    ⟨[315, 79003], [315, 79003], .contexts []⟩,
    ⟨[79003, 3], [79003, 3], .contexts []⟩,
    ⟨[79003, 5], [1887, 78519], .contexts [
        ⟨10279, true, false, [], [5]⟩,
        ⟨48, false, false, [78835], []⟩,
        ⟨51, false, false, [78835], []⟩,
        ⟨9738, false, false, [], [15]⟩,
        ⟨9739, false, false, [], [15]⟩,
        ⟨9325, false, false, [], [15]⟩,
        ⟨9326, false, false, [], [15]⟩,
        ⟨9326, false, false, [], [15]⟩,
        ⟨9339, false, false, [], []⟩,
        ⟨9332, false, false, [], []⟩,
        ⟨9333, false, false, [], []⟩,
        ⟨9333, false, false, [], []⟩,
        ⟨9334, false, false, [], []⟩,
        ⟨9338, false, false, [], []⟩
      ]⟩,
    ⟨[79003, 3, 1], [315, 2525, 78515], .contexts [
        ⟨10287, false, false, [], [1]⟩,
        ⟨10287, false, false, [], [1]⟩,
        ⟨10279, true, false, [], [3, 1]⟩,
        ⟨34, false, false, [78835], [1]⟩,
        ⟨37, false, false, [78835], [1]⟩,
        ⟨9734, false, false, [], [15, 1]⟩,
        ⟨9736, false, false, [], [15, 1]⟩,
        ⟨9732, false, false, [], [15, 1]⟩,
        ⟨9733, false, false, [], [15, 1]⟩,
        ⟨9733, false, false, [], [15, 1]⟩,
        ⟨10276, false, false, [315], [1]⟩,
        ⟨10285, false, false, [], [1]⟩,
        ⟨10286, false, false, [], [1]⟩,
        ⟨2812, true, false, [], [79003, 1]⟩,
        ⟨10285, false, false, [], [1]⟩,
        ⟨10286, false, false, [], [1]⟩,
        ⟨10286, false, false, [], [1]⟩,
        ⟨10283, false, false, [315], []⟩
      ]⟩,
    ⟨[2537], [315, 2525], .source 1333⟩,
    ⟨[78511, 3], [78511, 3], .contexts []⟩,
    ⟨[2539], [2527, 2537], .source 1334⟩,
    ⟨[78511, 3], [2539, 78515], .contexts [
        ⟨10291, false, false, [], []⟩,
        ⟨7846, true, false, [], [3]⟩,
        ⟨7849, true, false, [], [1, 3]⟩,
        ⟨10281, true, false, [2524], [3, 1, 3]⟩,
        ⟨10281, true, false, [2524], [3, 1, 3]⟩,
        ⟨10280, true, false, [2524], [3, 1, 3]⟩,
        ⟨10283, true, false, [2524], [3, 1, 3]⟩,
        ⟨10282, true, false, [2524], [3, 1, 3]⟩,
        ⟨852, false, false, [2524, 79003], []⟩,
        ⟨853, false, false, [2524, 79003], []⟩,
        ⟨10289, false, false, [2524], []⟩,
        ⟨10290, true, false, [2524], [78515]⟩,
        ⟨8173, false, false, [2524, 2537], []⟩,
        ⟨10231, true, false, [], [2537, 78515]⟩,
        ⟨10292, true, false, [], [78515]⟩
      ]⟩,
    ⟨[2541], [2538], .source 1335⟩,
    ⟨[78513], [2541, 78511], .contexts [
        ⟨8192, true, false, [], []⟩,
        ⟨10293, true, false, [2538], [3]⟩,
        ⟨35, false, false, [2538, 78511], []⟩,
        ⟨10294, true, false, [], [78511]⟩
      ]⟩,
    ⟨[2541, 78511], [2541, 78511], .contexts []⟩,
    ⟨[78513], [2541, 78511], .contexts [
        ⟨10295, false, false, [], []⟩,
        ⟨10296, false, false, [], []⟩
      ]⟩,
    ⟨[2543], [2539, 1899], .source 1336⟩,
    ⟨[78511, 9], [2543, 77679], .contexts [
        ⟨10295, true, false, [2540], [9]⟩,
        ⟨8193, true, false, [2540, 1900], [9]⟩,
        ⟨76, false, false, [2540, 1900, 77679], []⟩,
        ⟨8140, true, false, [2540], [77679]⟩,
        ⟨8191, false, false, [2540], []⟩,
        ⟨10294, false, true, [], [1899, 77679]⟩,
        ⟨10298, true, false, [], [77679]⟩
      ]⟩,
    ⟨[2539, 78515], [2539, 78515], .contexts []⟩,
    ⟨[2545], [2539, 2527], .source 1337⟩,
    ⟨[2547], [2544], .source 1338⟩,
    ⟨[2544], [2544], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 161. -/
def y322TCContextRaw161 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78991, 3], [2547, 78509], .contexts [
        ⟨10301, false, false, [2544], [78991, 3]⟩,
        ⟨10231, false, false, [2544, 2539], [78991, 3]⟩,
        ⟨3, true, false, [2544, 2539, 2524, 78991], [3]⟩,
        ⟨10230, false, false, [2544, 2539, 2524], [15, 3]⟩,
        ⟨10300, true, false, [2544], [15, 3]⟩,
        ⟨10300, true, false, [2544], [15, 3]⟩,
        ⟨10293, true, false, [2544], [15, 3]⟩,
        ⟨10291, true, false, [2544], [15, 3]⟩,
        ⟨900, false, false, [2544, 78511], []⟩,
        ⟨20, false, false, [2544, 78511], []⟩,
        ⟨7907, false, false, [2544], []⟩,
        ⟨7908, false, false, [2544], []⟩,
        ⟨7842, false, false, [2544], []⟩,
        ⟨7842, false, false, [2544], []⟩,
        ⟨8199, false, false, [2544], []⟩,
        ⟨10303, true, false, [], [78509]⟩,
        ⟨10303, true, false, [], [78509]⟩,
        ⟨10302, true, false, [], [78509]⟩
      ]⟩,
    ⟨[2549], [2541, 2543], .source 1339⟩,
    ⟨[2543, 77679], [2543, 77679], .contexts []⟩,
    ⟨[77677, 9], [77677, 9], .contexts []⟩,
    ⟨[2551], [2548], .source 1340⟩,
    ⟨[2553], [2551, 2543], .source 1341⟩,
    ⟨[77677, 9], [2553, 77677], .contexts [
        ⟨10307, false, false, [], []⟩,
        ⟨3845, true, false, [], [9]⟩,
        ⟨10305, false, false, [2548], [77679, 1, 9]⟩,
        ⟨10299, true, false, [2548, 2541], [1, 9]⟩,
        ⟨10296, true, false, [2548], [9, 1, 9]⟩,
        ⟨10296, true, false, [2548], [9, 1, 9]⟩,
        ⟨10297, true, false, [2548], [9, 1, 9]⟩,
        ⟨7844, true, false, [2548], [9, 1, 9]⟩,
        ⟨1022, false, false, [2548, 78511], []⟩,
        ⟨787, false, false, [2548, 78511], []⟩,
        ⟨10299, false, false, [2548], [1]⟩,
        ⟨10306, false, false, [2548], [1]⟩,
        ⟨10306, false, false, [2548], [1]⟩,
        ⟨3845, false, false, [2548, 2543], []⟩,
        ⟨7621, false, false, [2548, 2543], []⟩,
        ⟨10308, true, false, [], [2543, 77677]⟩,
        ⟨10309, true, false, [], [77677]⟩
      ]⟩,
    ⟨[2553, 77677], [2553, 77677], .contexts []⟩,
    ⟨[2561], [2552], .source 1345⟩,
    ⟨[2552], [2552], .contexts []⟩,
    ⟨[77675, 9], [2561, 77675], .contexts [
        ⟨3841, true, false, [], [9]⟩,
        ⟨10311, true, false, [2552], [15, 9]⟩,
        ⟨10311, true, false, [2552], [15, 9]⟩,
        ⟨10310, true, false, [2552], [15, 9]⟩,
        ⟨10307, true, false, [2552], [15, 9]⟩,
        ⟨1636, false, false, [2552, 77677], []⟩,
        ⟨7632, false, false, [2552], []⟩,
        ⟨7631, false, false, [2552], []⟩,
        ⟨7634, false, false, [2552], []⟩,
        ⟨10313, true, false, [], [77675]⟩,
        ⟨10313, true, false, [], [77675]⟩,
        ⟨10312, true, false, [], [77675]⟩
      ]⟩,
    ⟨[2561, 77675], [2561, 77675], .contexts []⟩,
    ⟨[79005], [77267, 7], .source 39567⟩,
    ⟨[77267, 7], [79005], .contexts [
        ⟨10316, true, false, [], []⟩
      ]⟩,
    ⟨[79005], [79005], .contexts []⟩,
    ⟨[79005], [79005], .contexts []⟩,
    ⟨[563, 77267], [563, 77267], .contexts []⟩,
    ⟨[77269], [563, 77267], .contexts [
        ⟨2904, false, false, [], []⟩,
        ⟨10320, false, false, [], []⟩
      ]⟩,
    ⟨[77269], [563, 77267], .contexts [
        ⟨10321, false, false, [], []⟩
      ]⟩,
    ⟨[563, 79005], [563, 79005], .contexts []⟩,
    ⟨[563, 79005], [563, 79005], .contexts []⟩,
    ⟨[79005, 1], [79005, 1], .contexts []⟩,
    ⟨[79005], [79005], .contexts []⟩,
    ⟨[563], [563], .contexts [
        ⟨24, false, false, [], [563]⟩
      ]⟩,
    ⟨[77267, 3], [1755, 77141], .contexts [
        ⟨9189, true, false, [1752], [3]⟩,
        ⟨35, false, false, [1752, 77141], []⟩,
        ⟨7545, true, false, [], [77141]⟩,
        ⟨9184, false, false, [], []⟩,
        ⟨9185, false, false, [], []⟩,
        ⟨9185, false, false, [], []⟩
      ]⟩,
    ⟨[1755], [1755], .contexts [
        ⟨24, false, false, [], [1755]⟩
      ]⟩,
    ⟨[79007], [77267, 13], .source 39568⟩,
    ⟨[77267, 13], [79007], .contexts [
        ⟨10330, true, false, [], []⟩
      ]⟩,
    ⟨[79007, 13], [77267], .contexts [
        ⟨10331, true, false, [], [13]⟩,
        ⟨98, false, false, [77267], []⟩,
        ⟨1223, false, false, [], []⟩
      ]⟩,
    ⟨[77267, 13], [79007], .contexts [
        ⟨10331, false, false, [], []⟩
      ]⟩,
    ⟨[79007], [79007], .contexts []⟩,
    ⟨[77267, 13], [79007], .contexts [
        ⟨10333, false, false, [], []⟩,
        ⟨10334, false, false, [], []⟩,
        ⟨10334, false, false, [], []⟩
      ]⟩,
    ⟨[1755, 78995], [1755, 78995], .contexts []⟩,
    ⟨[1755, 78995], [1755, 78995], .contexts []⟩,
    ⟨[79007, 3], [79007, 3], .contexts []⟩,
    ⟨[79007, 3], [1755, 78995], .contexts [
        ⟨10338, false, false, [], []⟩,
        ⟨10335, true, false, [], [3]⟩,
        ⟨107, false, false, [77267], []⟩,
        ⟨109, false, false, [77267], []⟩,
        ⟨10328, false, false, [], [13]⟩,
        ⟨10249, false, false, [1755], []⟩,
        ⟨10336, false, false, [], []⟩,
        ⟨10337, false, false, [], []⟩,
        ⟨10254, false, false, [1755], []⟩,
        ⟨10329, true, false, [], [78995]⟩
      ]⟩,
    ⟨[78995, 3], [1753, 79007], .contexts [
        ⟨10339, true, false, [1754], [3]⟩,
        ⟨35, false, false, [1754, 79007], []⟩,
        ⟨9171, true, false, [], [79007]⟩
      ]⟩,
    ⟨[2565], [1755, 2535], .source 1347⟩,
    ⟨[2567], [2565, 1753], .source 1348⟩,
    ⟨[2569], [2566], .source 1349⟩,
    ⟨[2566], [2566], .contexts []⟩,
    ⟨[79007, 15], [2569, 79007], .contexts [
        ⟨10342, false, false, [2566], [79007, 15]⟩,
        ⟨10340, true, false, [2566, 2565], [15]⟩,
        ⟨10341, false, false, [2566], [78995, 3, 15]⟩,
        ⟨10263, true, false, [2566, 1755], [3, 15]⟩,
        ⟨10337, true, false, [2566], [15, 3, 15]⟩,
        ⟨10337, true, false, [2566], [15, 3, 15]⟩,
        ⟨10336, true, false, [2566], [15, 3, 15]⟩,
        ⟨10339, true, false, [2566], [15, 3, 15]⟩,
        ⟨10338, true, false, [2566], [15, 3, 15]⟩,
        ⟨2767, false, false, [2566, 79007], []⟩,
        ⟨10344, true, false, [], [79007]⟩,
        ⟨10344, true, false, [], [79007]⟩,
        ⟨10343, true, false, [], [79007]⟩
      ]⟩,
    ⟨[79009], [77267, 15], .source 39569⟩,
    ⟨[77267, 15], [79009], .contexts [
        ⟨10346, true, false, [], []⟩
      ]⟩,
    ⟨[79009], [79009], .contexts []⟩,
    ⟨[77267, 15], [79009], .contexts [
        ⟨10347, false, false, [], []⟩,
        ⟨10348, false, false, [], []⟩,
        ⟨10348, false, false, [], []⟩
      ]⟩,
    ⟨[2571], [1755, 1887], .source 1350⟩,
    ⟨[2573], [2570], .source 1351⟩,
    ⟨[2569, 79007], [2569, 79007], .contexts []⟩,
    ⟨[79015], [78987, 9], .source 39572⟩,
    ⟨[79015], [79015], .contexts []⟩,
    ⟨[78987, 7], [77141], .contexts [
        ⟨10188, true, false, [], [7]⟩,
        ⟨62, false, false, [77141], []⟩,
        ⟨463, false, false, [], []⟩,
        ⟨710, false, false, [], []⟩,
        ⟨463, false, false, [], []⟩,
        ⟨463, false, false, [], []⟩
      ]⟩,
    ⟨[79015, 7], [79015, 7], .contexts []⟩,
    ⟨[79017], [78987, 11], .source 39573⟩,
    ⟨[79017], [79017], .contexts []⟩,
    ⟨[79017], [79017], .contexts []⟩,
    ⟨[78993], [78993], .contexts []⟩,
    ⟨[78993], [78993], .contexts [
        ⟨1118, true, false, [], [78993]⟩
      ]⟩,
    ⟨[79019], [78987, 13], .source 39574⟩,
    ⟨[78987, 13], [79019], .contexts [
        ⟨10362, true, false, [], []⟩
      ]⟩,
    ⟨[79019], [79019], .contexts []⟩,
    ⟨[78987, 13], [79019], .contexts [
        ⟨10363, false, false, [], []⟩,
        ⟨10364, false, false, [], []⟩,
        ⟨10364, false, false, [], []⟩
      ]⟩,
    ⟨[79019, 7], [79019, 7], .contexts []⟩,
    ⟨[78995], [78995], .contexts [
        ⟨10254, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 162. -/
def y322TCContextRaw162 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78995], [78995], .contexts [
        ⟨1118, true, false, [], [78995]⟩
      ]⟩,
    ⟨[79019, 7], [78995], .contexts [
        ⟨10366, false, false, [], []⟩,
        ⟨10365, true, false, [], [7]⟩,
        ⟨124, false, false, [78987], []⟩,
        ⟨125, false, false, [78987], []⟩,
        ⟨10355, false, false, [], [13]⟩,
        ⟨10250, false, false, [], []⟩,
        ⟨10251, false, false, [], []⟩,
        ⟨10252, false, false, [], []⟩,
        ⟨10252, false, false, [], []⟩,
        ⟨10367, false, false, [], []⟩,
        ⟨10368, false, false, [], []⟩
      ]⟩,
    ⟨[2575], [2534], .source 1352⟩,
    ⟨[2534], [2534], .contexts []⟩,
    ⟨[2575], [2534], .contexts [
        ⟨10370, false, false, [], []⟩,
        ⟨10371, false, false, [], []⟩,
        ⟨10371, false, false, [], []⟩
      ]⟩,
    ⟨[79019, 15], [2575, 79019], .contexts [
        ⟨10364, true, false, [], [15]⟩,
        ⟨62, true, false, [79019], [15]⟩,
        ⟨10369, false, false, [], [7, 15]⟩,
        ⟨10260, true, false, [2534], [7, 15]⟩,
        ⟨10260, true, false, [2534], [7, 15]⟩,
        ⟨10259, true, false, [2534], [7, 15]⟩,
        ⟨10263, true, false, [2534], [7, 15]⟩,
        ⟨10252, true, false, [2534], [15, 7, 15]⟩,
        ⟨10252, true, false, [2534], [15, 7, 15]⟩,
        ⟨10251, true, false, [2534], [15, 7, 15]⟩,
        ⟨10369, true, false, [2534], [15, 7, 15]⟩,
        ⟨10366, true, false, [2534], [15, 7, 15]⟩,
        ⟨5803, false, false, [2534, 79019], []⟩,
        ⟨10372, true, false, [], [79019]⟩
      ]⟩,
    ⟨[79021], [78987, 15], .source 39575⟩,
    ⟨[78987, 15], [79021], .contexts [
        ⟨10374, true, false, [], []⟩
      ]⟩,
    ⟨[79021], [79021], .contexts []⟩,
    ⟨[79021], [79021], .contexts []⟩,
    ⟨[78987, 15], [79021], .contexts [
        ⟨10375, false, false, [], []⟩,
        ⟨10376, false, false, [], []⟩,
        ⟨10377, false, false, [], []⟩,
        ⟨10377, false, false, [], []⟩
      ]⟩,
    ⟨[78987, 1, 15], [79001], .contexts [
        ⟨10191, false, false, [], [15]⟩,
        ⟨10191, false, false, [], [15]⟩,
        ⟨10189, true, false, [], [1, 15]⟩,
        ⟨10189, true, false, [], [1, 15]⟩,
        ⟨10188, true, false, [], [1, 15]⟩,
        ⟨1764, false, false, [77141], [15]⟩,
        ⟨1765, false, false, [77141], [15]⟩,
        ⟨10190, false, false, [], [7, 15]⟩,
        ⟨9717, false, false, [], [15]⟩,
        ⟨9718, false, false, [], [15]⟩,
        ⟨9719, false, false, [], [15]⟩,
        ⟨9719, false, false, [], [15]⟩,
        ⟨1118, true, false, [], [78829, 15]⟩,
        ⟨9718, false, false, [], [15]⟩,
        ⟨9719, false, false, [], [15]⟩,
        ⟨9719, false, false, [], [15]⟩,
        ⟨10265, false, false, [], []⟩,
        ⟨10266, false, false, [], []⟩,
        ⟨10267, false, false, [], []⟩,
        ⟨10267, false, false, [], []⟩
      ]⟩,
    ⟨[2575, 79019], [2575, 79019], .contexts []⟩,
    ⟨[2575, 79021], [2575, 79021], .contexts []⟩,
    ⟨[2575, 79021], [2575, 79021], .contexts []⟩,
    ⟨[79021, 13], [79021, 13], .contexts []⟩,
    ⟨[2575], [2575], .contexts [
        ⟨24, false, false, [], [2575]⟩
      ]⟩,
    ⟨[79023], [77145, 9], .source 39576⟩,
    ⟨[77145, 9], [79023], .contexts [
        ⟨10385, true, false, [], []⟩
      ]⟩,
    ⟨[77145, 9], [79023], .contexts [
        ⟨10386, false, false, [], []⟩
      ]⟩,
    ⟨[79023], [79023], .contexts []⟩,
    ⟨[79023], [79023], .contexts []⟩,
    ⟨[77145, 9], [79023], .contexts [
        ⟨10387, false, false, [], []⟩,
        ⟨10388, false, false, [], []⟩,
        ⟨10389, false, false, [], []⟩,
        ⟨10389, false, false, [], []⟩
      ]⟩,
    ⟨[2007, 79023], [2007, 79023], .contexts []⟩,
    ⟨[2007, 79023], [2007, 79023], .contexts []⟩,
    ⟨[79023, 1], [79023, 1], .contexts []⟩,
    ⟨[79023], [79023], .contexts []⟩,
    ⟨[79023, 1], [2007, 79023], .contexts [
        ⟨10393, false, false, [], []⟩,
        ⟨10390, true, false, [], [1]⟩,
        ⟨1143, false, false, [77145], []⟩,
        ⟨1146, false, false, [77145], []⟩,
        ⟨10204, false, false, [], [9, 1, 9]⟩,
        ⟨704, false, false, [], [9, 1, 9]⟩,
        ⟨474, false, false, [], [9, 1, 9]⟩,
        ⟨474, false, false, [], [9, 1, 9]⟩,
        ⟨8491, false, false, [], [1, 9]⟩,
        ⟨8492, false, false, [], [1, 9]⟩,
        ⟨8493, false, false, [], [1, 9]⟩,
        ⟨8493, false, false, [], [1, 9]⟩,
        ⟨471, false, false, [2007], [9]⟩,
        ⟨10386, false, false, [2007], []⟩,
        ⟨10391, false, false, [], []⟩,
        ⟨10392, false, false, [], []⟩,
        ⟨10394, false, false, [2007], []⟩
      ]⟩,
    ⟨[2209, 77273], [2209, 77273], .contexts []⟩,
    ⟨[77145, 3], [2209, 77273], .contexts [
        ⟨9202, false, false, [], []⟩,
        ⟨9204, false, false, [], []⟩,
        ⟨10396, false, false, [], []⟩,
        ⟨10396, false, false, [], []⟩
      ]⟩,
    ⟨[2577], [2209, 1491], .source 1353⟩,
    ⟨[79023, 3], [79023, 3], .contexts []⟩,
    ⟨[2577], [2577], .contexts [
        ⟨24, false, false, [], [2577]⟩
      ]⟩,
    ⟨[79023, 3], [2577, 78289], .contexts [
        ⟨10399, false, false, [], []⟩,
        ⟨10390, true, false, [], [3]⟩,
        ⟨306, false, false, [77145], []⟩,
        ⟨307, false, false, [77145], []⟩,
        ⟨10397, false, false, [], [9]⟩,
        ⟨24, false, false, [2209, 1488], [1489, 77273, 9]⟩,
        ⟨6924, true, false, [2209, 1488], [9]⟩,
        ⟨76, false, false, [2209, 1488, 78289], []⟩,
        ⟨6925, true, false, [2209], [78289]⟩,
        ⟨10398, true, false, [], [78289]⟩,
        ⟨10400, true, false, [], [78289]⟩
      ]⟩,
    ⟨[2579], [2576], .source 1354⟩,
    ⟨[2581], [2007, 2577], .source 1355⟩,
    ⟨[2577, 78289], [2577, 78289], .contexts []⟩,
    ⟨[79023, 3], [2577, 78289], .contexts [
        ⟨10399, false, false, [], []⟩,
        ⟨10401, false, false, [], []⟩,
        ⟨10404, false, false, [], []⟩,
        ⟨10404, false, false, [], []⟩
      ]⟩,
    ⟨[78291, 3], [78291, 3], .contexts []⟩,
    ⟨[78291, 3], [2580, 2577, 78291], .contexts [
        ⟨10406, false, false, [], []⟩,
        ⟨6927, true, false, [], [3]⟩,
        ⟨10403, false, false, [2580], [78289, 1, 3]⟩,
        ⟨10401, true, false, [2580, 2007], [1, 3]⟩,
        ⟨10392, true, false, [2580], [3, 1, 3]⟩,
        ⟨10392, true, false, [2580], [3, 1, 3]⟩,
        ⟨10391, true, false, [2580], [3, 1, 3]⟩,
        ⟨10224, false, false, [2580], [79023, 3, 1, 3]⟩,
        ⟨10395, true, false, [2580], [3, 1, 3]⟩,
        ⟨10393, true, false, [2580], [3, 1, 3]⟩,
        ⟨852, false, false, [2580, 79023], []⟩,
        ⟨853, false, false, [2580, 79023], []⟩,
        ⟨10405, false, false, [2580], [1]⟩,
        ⟨6927, false, false, [2580, 2577], []⟩
      ]⟩,
    ⟨[2583], [2580], .source 1356⟩,
    ⟨[2585], [2583, 2577], .source 1357⟩,
    ⟨[2585, 78291], [2585, 78291], .contexts []⟩,
    ⟨[78291, 13], [78293], .contexts [
        ⟨6929, false, false, [], []⟩,
        ⟨7154, false, false, [], []⟩,
        ⟨6933, false, false, [], []⟩,
        ⟨6933, false, false, [], []⟩
      ]⟩,
    ⟨[2585, 78293, 3], [78291, 13], .contexts [
        ⟨6929, true, false, [2585], [3]⟩,
        ⟨10410, true, false, [], [13, 3]⟩,
        ⟨10410, true, false, [], [13, 3]⟩,
        ⟨10409, false, false, [], [78291, 13, 3]⟩,
        ⟨10408, false, false, [], [2577, 78291, 13, 3]⟩,
        ⟨10407, true, false, [], [13, 3]⟩,
        ⟨10406, true, false, [], [13, 3]⟩,
        ⟨932, false, false, [78291], []⟩,
        ⟨108, false, false, [78291], []⟩
      ]⟩,
    ⟨[78293, 3], [78293, 3], .contexts []⟩,
    ⟨[2587], [2584], .source 1358⟩,
    ⟨[2587], [2587], .contexts []⟩,
    ⟨[2587], [2584], .contexts [
        ⟨10414, false, false, [], []⟩
      ]⟩,
    ⟨[2584], [2584], .contexts []⟩,
    ⟨[2587], [2584], .contexts [
        ⟨10415, false, false, [], []⟩,
        ⟨10416, false, false, [], []⟩,
        ⟨10417, false, false, [], []⟩,
        ⟨10417, false, false, [], []⟩
      ]⟩,
    ⟨[2587, 78293], [2587, 78293], .contexts []⟩,
    ⟨[78293, 15], [78295], .contexts [
        ⟨6932, false, false, [], []⟩,
        ⟨7152, false, false, [], []⟩,
        ⟨6936, false, false, [], []⟩,
        ⟨6936, false, false, [], []⟩
      ]⟩,
    ⟨[78295, 3], [78295, 3], .contexts []⟩,
    ⟨[78295, 3], [2586, 78295], .contexts [
        ⟨10421, false, false, [], []⟩,
        ⟨6932, true, false, [], [3]⟩,
        ⟨10419, true, false, [2586], [15, 3]⟩,
        ⟨10419, true, false, [2586], [15, 3]⟩,
        ⟨10418, false, false, [2586], [78293, 15, 3]⟩,
        ⟨10411, true, false, [2586, 2584], [15, 3]⟩,
        ⟨10412, true, false, [2586, 2584], [15, 3]⟩,
        ⟨10413, true, false, [2586], [15, 3]⟩,
        ⟨10413, true, false, [2586], [15, 3]⟩,
        ⟨900, false, false, [2586, 78293], []⟩,
        ⟨20, false, false, [2586, 78293], []⟩,
        ⟨10420, false, false, [2586], []⟩
      ]⟩,
    ⟨[2585], [2586], .contexts [
        ⟨10414, true, true, [], []⟩
      ]⟩,
    ⟨[2586], [2586], .contexts []⟩,
    ⟨[2585], [2586], .contexts [
        ⟨10423, false, false, [], []⟩,
        ⟨10424, false, false, [], []⟩,
        ⟨10424, false, false, [], []⟩
      ]⟩,
    ⟨[2585, 78295], [2585, 78295], .contexts []⟩,
    ⟨[78295, 1], [78297], .contexts [
        ⟨6935, false, false, [], []⟩
      ]⟩,
    ⟨[78297, 3], [78299], .contexts [
        ⟨6938, false, false, [], []⟩
      ]⟩,
    ⟨[78299, 1], [78299, 1], .contexts []⟩,
    ⟨[78299, 1], [2584, 78299], .contexts [
        ⟨10429, false, false, [], []⟩,
        ⟨6938, true, false, [], [1]⟩,
        ⟨6935, true, false, [], [3, 1]⟩,
        ⟨10426, true, false, [2584], [1, 3, 1]⟩,
        ⟨10426, true, false, [2584], [1, 3, 1]⟩,
        ⟨10425, false, false, [2584], [78295, 1, 3, 1]⟩,
        ⟨10422, true, false, [2584], [1, 3, 1]⟩,
        ⟨10421, true, false, [2584], [1, 3, 1]⟩,
        ⟨2891, false, false, [2584, 78295], []⟩,
        ⟨214, false, false, [2584, 78295], []⟩,
        ⟨10427, false, false, [2584], [3]⟩,
        ⟨7151, false, false, [2584], [3]⟩,
        ⟨6939, false, false, [2584], [3]⟩,
        ⟨6939, false, false, [2584], [3]⟩,
        ⟨10428, false, false, [2584], []⟩,
        ⟨7150, false, false, [2584], []⟩,
        ⟨6943, false, false, [2584], []⟩,
        ⟨6943, false, false, [2584], []⟩
      ]⟩,
    ⟨[78299], [78299], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 163. -/
def y322TCContextRaw163 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2587, 78299], [2587, 78299], .contexts []⟩,
    ⟨[2587, 78303], [2587, 78303], .contexts []⟩,
    ⟨[78303, 5], [2586, 78299], .contexts [
        ⟨10433, true, false, [2586], [5]⟩,
        ⟨6945, true, false, [], [5]⟩,
        ⟨6942, true, false, [], [1, 5]⟩,
        ⟨10432, true, false, [2586], [5, 1, 5]⟩,
        ⟨10432, true, false, [2586], [5, 1, 5]⟩,
        ⟨10418, false, false, [2586], [78299, 5, 1, 5]⟩,
        ⟨10431, true, false, [2586, 2584], [5, 1, 5]⟩,
        ⟨10430, true, false, [2586], [5, 1, 5]⟩,
        ⟨10429, true, false, [2586], [5, 1, 5]⟩,
        ⟨1909, false, false, [2586, 78299], []⟩
      ]⟩,
    ⟨[78299, 5], [78301], .contexts [
        ⟨6942, false, false, [], []⟩
      ]⟩,
    ⟨[79025], [79023, 11], .source 39577⟩,
    ⟨[79023, 11], [79025], .contexts [
        ⟨10436, true, false, [], []⟩
      ]⟩,
    ⟨[79025], [79025], .contexts []⟩,
    ⟨[79025], [79025], .contexts []⟩,
    ⟨[79023, 11], [79025], .contexts [
        ⟨10437, false, false, [], []⟩,
        ⟨10438, false, false, [], []⟩,
        ⟨10439, false, false, [], []⟩,
        ⟨10439, false, false, [], []⟩
      ]⟩,
    ⟨[79023, 9], [77145], .contexts [
        ⟨10386, true, false, [], [9]⟩,
        ⟨76, false, false, [77145], []⟩,
        ⟨470, false, false, [], []⟩,
        ⟨706, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩
      ]⟩,
    ⟨[78993, 9], [79025], .contexts [
        ⟨10361, true, false, [], [9]⟩,
        ⟨10360, true, false, [], [9]⟩,
        ⟨10236, true, false, [], [9]⟩,
        ⟨10236, true, false, [], [9]⟩,
        ⟨10235, true, false, [], [9]⟩,
        ⟨10234, true, false, [], [9]⟩,
        ⟨463, true, false, [], [11, 9]⟩,
        ⟨463, true, false, [], [11, 9]⟩,
        ⟨710, true, false, [], [11, 9]⟩,
        ⟨709, true, false, [], [11, 9]⟩,
        ⟨467, true, false, [], [9, 11, 9]⟩,
        ⟨467, true, false, [], [9, 11, 9]⟩,
        ⟨708, true, false, [], [9, 11, 9]⟩,
        ⟨707, true, false, [], [9, 11, 9]⟩,
        ⟨10441, true, false, [], [11, 9, 11, 9]⟩,
        ⟨346, true, false, [79023], [9]⟩,
        ⟨344, true, false, [79023], [9]⟩,
        ⟨10440, false, false, [], [9, 9]⟩,
        ⟨76, false, false, [79025], []⟩,
        ⟨10439, false, false, [], []⟩
      ]⟩,
    ⟨[79027], [77143, 13], .source 39578⟩,
    ⟨[77143, 13], [79027], .contexts [
        ⟨10443, true, false, [], []⟩
      ]⟩,
    ⟨[77143, 13], [79027], .contexts [
        ⟨10444, false, false, [], []⟩
      ]⟩,
    ⟨[79027], [79027], .contexts []⟩,
    ⟨[79027], [79027], .contexts []⟩,
    ⟨[77143, 13], [79027], .contexts [
        ⟨10445, false, false, [], []⟩,
        ⟨10446, false, false, [], []⟩,
        ⟨10447, false, false, [], []⟩,
        ⟨10447, false, false, [], []⟩
      ]⟩,
    ⟨[79027, 5], [79027, 5], .contexts []⟩,
    ⟨[79027, 5], [2191, 77573], .contexts [
        ⟨10449, false, false, [], []⟩,
        ⟨10448, true, false, [], [5]⟩,
        ⟨116, false, false, [77143], []⟩,
        ⟨117, false, false, [77143], []⟩,
        ⟨10198, false, false, [], [13]⟩,
        ⟨9651, false, false, [], []⟩,
        ⟨9646, false, false, [], []⟩,
        ⟨9647, false, false, [], []⟩,
        ⟨9647, false, false, [], []⟩,
        ⟨9648, false, false, [], []⟩,
        ⟨9650, false, false, [], []⟩
      ]⟩,
    ⟨[79027, 9], [78995], .contexts [
        ⟨10448, true, false, [], [9]⟩,
        ⟨130, false, false, [77143], []⟩,
        ⟨131, false, false, [77143], []⟩,
        ⟨709, false, false, [], [13]⟩,
        ⟨710, false, false, [], [13]⟩,
        ⟨463, false, false, [], [13]⟩,
        ⟨463, false, false, [], [13]⟩,
        ⟨10250, false, false, [], []⟩,
        ⟨10251, false, false, [], []⟩,
        ⟨10252, false, false, [], []⟩,
        ⟨10252, false, false, [], []⟩,
        ⟨10367, false, false, [], []⟩,
        ⟨10368, false, false, [], []⟩
      ]⟩,
    ⟨[79027], [79027], .contexts []⟩,
    ⟨[2191, 77569], [2191, 77569], .contexts []⟩,
    ⟨[2191, 77569], [2191, 77569], .contexts []⟩,
    ⟨[77569, 1], [2193, 79027], .contexts [
        ⟨10454, true, false, [2190], [1]⟩,
        ⟨10453, true, false, [2190], [1]⟩,
        ⟨3096, true, false, [], [1]⟩,
        ⟨3099, true, false, [], [5, 1]⟩,
        ⟨9647, true, false, [2190], [1, 5, 1]⟩,
        ⟨9647, true, false, [2190], [1, 5, 1]⟩,
        ⟨9646, true, false, [2190], [1, 5, 1]⟩,
        ⟨10450, true, false, [2190], [1, 5, 1]⟩,
        ⟨10449, true, false, [2190], [1, 5, 1]⟩,
        ⟨1485, false, false, [2190, 79027], []⟩,
        ⟨10452, false, false, [2190], []⟩,
        ⟨9139, true, false, [], [79027]⟩
      ]⟩,
    ⟨[79029], [78993, 13], .source 39579⟩,
    ⟨[78993, 13], [79029], .contexts [
        ⟨10456, true, false, [], []⟩
      ]⟩,
    ⟨[79029], [79029], .contexts []⟩,
    ⟨[78993, 13], [79029], .contexts [
        ⟨10457, false, false, [], []⟩,
        ⟨10458, false, false, [], []⟩,
        ⟨10458, false, false, [], []⟩
      ]⟩,
    ⟨[78993, 1, 13, 1, 13], [1075, 79029], .contexts [
        ⟨10238, false, false, [], [13, 1, 13]⟩,
        ⟨10239, false, false, [], [13, 1, 13]⟩,
        ⟨9743, false, false, [], [13, 1, 13]⟩,
        ⟨9744, false, false, [], [13, 1, 13]⟩,
        ⟨9744, false, false, [], [13, 1, 13]⟩,
        ⟨9745, true, false, [], [13, 1, 13]⟩,
        ⟨352, false, false, [77139], [1, 13]⟩,
        ⟨353, false, false, [77139], [1, 13]⟩,
        ⟨9724, false, false, [], [11, 1, 13]⟩,
        ⟨9741, false, false, [1075], [1, 13]⟩,
        ⟨9750, false, false, [], [1, 13]⟩,
        ⟨9751, false, false, [], [1, 13]⟩,
        ⟨9746, false, false, [1075], [1, 13]⟩,
        ⟨9215, true, false, [], [78837, 1, 13]⟩,
        ⟨9750, false, false, [], [1, 13]⟩,
        ⟨9751, false, false, [], [1, 13]⟩,
        ⟨9751, false, false, [], [1, 13]⟩,
        ⟨10239, true, false, [1075], [1, 13]⟩,
        ⟨18, false, false, [1075, 78993], [13]⟩,
        ⟨10236, false, false, [1075], [13]⟩,
        ⟨10457, false, false, [1075], []⟩
      ]⟩,
    ⟨[78995, 11], [79029], .contexts [
        ⟨10368, true, false, [], [11]⟩,
        ⟨10367, true, false, [], [11]⟩,
        ⟨10252, true, false, [], [11]⟩,
        ⟨10252, true, false, [], [11]⟩,
        ⟨10251, true, false, [], [11]⟩,
        ⟨10250, true, false, [], [11]⟩,
        ⟨463, true, false, [], [13, 11]⟩,
        ⟨463, true, false, [], [13, 11]⟩,
        ⟨710, true, false, [], [13, 11]⟩,
        ⟨463, true, false, [], [13, 11]⟩,
        ⟨90, true, false, [77141], [13, 11]⟩,
        ⟨10233, false, false, [], [11, 13, 11]⟩,
        ⟨138, true, false, [78993], [11]⟩,
        ⟨137, true, false, [78993], [11]⟩,
        ⟨10459, false, false, [], [11, 11]⟩,
        ⟨90, false, false, [79029], []⟩,
        ⟨10458, false, false, [], []⟩
      ]⟩,
    ⟨[79031], [78825, 11], .source 39580⟩,
    ⟨[78825, 11], [79031], .contexts [
        ⟨10462, true, false, [], []⟩
      ]⟩,
    ⟨[79031, 11], [78825], .contexts [
        ⟨10463, true, false, [], [11]⟩,
        ⟨90, false, false, [78825], []⟩,
        ⟨9638, false, false, [], []⟩
      ]⟩,
    ⟨[79031], [79031], .contexts []⟩,
    ⟨[79031], [79031], .contexts []⟩,
    ⟨[79031, 5], [79031, 5], .contexts []⟩,
    ⟨[77145], [77145], .contexts [
        ⟨8458, false, false, [], []⟩
      ]⟩,
    ⟨[77145], [77145], .contexts [
        ⟨1118, true, false, [], [77145]⟩
      ]⟩,
    ⟨[79031, 5], [77145], .contexts [
        ⟨10467, false, false, [], []⟩,
        ⟨10466, true, false, [], [5]⟩,
        ⟨10466, true, false, [], [5]⟩,
        ⟨10465, true, false, [], [5]⟩,
        ⟨10463, true, false, [], [5]⟩,
        ⟨1083, false, false, [78825], []⟩,
        ⟨1084, false, false, [78825], []⟩,
        ⟨9640, false, false, [], [11]⟩,
        ⟨9643, false, false, [], [11]⟩,
        ⟨708, false, false, [], [11]⟩,
        ⟨467, false, false, [], [11]⟩,
        ⟨467, false, false, [], [11]⟩,
        ⟨10203, false, false, [], []⟩,
        ⟨706, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩,
        ⟨10468, false, false, [], []⟩,
        ⟨10469, false, false, [], []⟩
      ]⟩,
    ⟨[79033], [79031, 1], .source 39581⟩,
    ⟨[79031, 1], [79033], .contexts [
        ⟨10471, true, false, [], []⟩
      ]⟩,
    ⟨[79033, 1], [79031], .contexts [
        ⟨10472, true, false, [], [1]⟩,
        ⟨18, false, false, [79031], []⟩,
        ⟨10466, false, false, [], []⟩
      ]⟩,
    ⟨[79033], [79033], .contexts []⟩,
    ⟨[79033], [79033], .contexts []⟩,
    ⟨[79031, 1], [79033], .contexts [
        ⟨10472, false, false, [], []⟩,
        ⟨10474, false, false, [], []⟩,
        ⟨10475, false, false, [], []⟩,
        ⟨10475, false, false, [], []⟩
      ]⟩,
    ⟨[79031, 5], [77145], .contexts [
        ⟨10470, false, false, [], []⟩
      ]⟩,
    ⟨[79031, 5], [77145], .contexts [
        ⟨10467, false, false, [], []⟩,
        ⟨10477, false, false, [], []⟩,
        ⟨706, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩
      ]⟩,
    ⟨[79033, 5], [79033, 5], .contexts []⟩,
    ⟨[79033, 5], [77147], .contexts [
        ⟨10479, false, false, [], []⟩,
        ⟨10476, true, false, [], [5]⟩,
        ⟨165, false, false, [79031], []⟩,
        ⟨166, false, false, [79031], []⟩,
        ⟨10478, false, false, [], [1]⟩,
        ⟨10204, false, false, [], []⟩,
        ⟨704, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩,
        ⟨10206, false, false, [], []⟩,
        ⟨10207, false, false, [], []⟩
      ]⟩,
    ⟨[77147, 5], [79033], .contexts [
        ⟨10480, true, false, [], [5]⟩,
        ⟨49, false, false, [79033], []⟩,
        ⟨10475, false, false, [], []⟩
      ]⟩,
    ⟨[79033, 11], [79033, 11], .contexts []⟩,
    ⟨[79033, 11], [78827], .contexts [
        ⟨10482, false, false, [], []⟩,
        ⟨10476, true, false, [], [11]⟩,
        ⟨181, false, false, [79031], []⟩,
        ⟨182, false, false, [79031], []⟩,
        ⟨10464, false, false, [], [1]⟩,
        ⟨9637, false, false, [], [1]⟩,
        ⟨9638, false, false, [], [1]⟩,
        ⟨9638, false, false, [], [1]⟩,
        ⟨9658, false, false, [], []⟩,
        ⟨9659, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨10200, false, false, [], []⟩,
        ⟨10201, false, false, [], []⟩
      ]⟩,
    ⟨[79033, 5], [77147], .contexts [
        ⟨10480, false, false, [], []⟩
      ]⟩,
    ⟨[79033, 5], [77147], .contexts [
        ⟨10479, false, false, [], []⟩,
        ⟨10484, false, false, [], []⟩,
        ⟨704, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩,
        ⟨474, false, false, [], []⟩
      ]⟩,
    ⟨[79033], [79033], .contexts []⟩,
    ⟨[79033, 9], [79033, 9], .contexts []⟩,
    ⟨[79033], [79033], .contexts []⟩,
    ⟨[79033, 11], [78827], .contexts [
        ⟨10482, false, false, [], []⟩,
        ⟨10483, false, false, [], []⟩,
        ⟨9659, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩,
        ⟨9660, false, false, [], []⟩
      ]⟩,
    ⟨[78827, 3], [2375, 78827], .contexts [
        ⟨9678, false, false, [2372], [78827, 3]⟩,
        ⟨9582, false, false, [2372, 2371], [78827, 3]⟩,
        ⟨76, true, false, [2372, 2371, 2324, 78827], [3]⟩,
        ⟨9668, false, false, [2372, 2371, 2324], [9, 3]⟩,
        ⟨9677, true, false, [2372], [9, 3]⟩,
        ⟨2415, false, false, [2372, 78827], []⟩,
        ⟨9679, false, false, [2372], []⟩,
        ⟨9680, false, false, [2372], []⟩,
        ⟨9683, true, false, [], [78827]⟩
      ]⟩,
    ⟨[2375, 78827], [2375, 78827], .contexts []⟩,
    ⟨[2375, 78827], [2375, 78827], .contexts []⟩,
    ⟨[79033, 3], [79033, 3], .contexts []⟩,
    ⟨[2374], [2374], .contexts []⟩,
    ⟨[2373], [2374], .contexts [
        ⟨9681, true, true, [], []⟩,
        ⟨10494, false, false, [], []⟩,
        ⟨10494, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 164. -/
def y322TCContextRaw164 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79035], [79033, 13], .source 39582⟩,
    ⟨[79033, 13], [79035], .contexts [
        ⟨10496, true, false, [], []⟩
      ]⟩,
    ⟨[79035, 13], [79033], .contexts [
        ⟨10497, true, false, [], [13]⟩,
        ⟨98, false, false, [79033], []⟩,
        ⟨10475, false, false, [], []⟩
      ]⟩,
    ⟨[79035], [79035], .contexts []⟩,
    ⟨[79035], [79035], .contexts []⟩,
    ⟨[79033, 13], [79035], .contexts [
        ⟨10497, false, false, [], []⟩,
        ⟨10499, false, false, [], []⟩,
        ⟨10500, false, false, [], []⟩,
        ⟨10500, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 79033], [2373, 79033], .contexts []⟩,
    ⟨[79033, 3], [2373, 79033], .contexts [
        ⟨10493, false, false, [], []⟩,
        ⟨10493, false, false, [], []⟩,
        ⟨10475, true, false, [], [3]⟩,
        ⟨90, true, false, [79033], [3]⟩,
        ⟨10483, false, false, [], [11, 3]⟩,
        ⟨10492, true, false, [2374], [11, 3]⟩,
        ⟨10492, true, false, [2374], [11, 3]⟩,
        ⟨10491, true, false, [2374], [11, 3]⟩,
        ⟨10490, true, false, [2374], [11, 3]⟩,
        ⟨10489, true, false, [2374], [3, 11, 3]⟩,
        ⟨6162, false, false, [2374, 79033], []⟩,
        ⟨10486, false, false, [2374], []⟩,
        ⟨10488, false, false, [2374], []⟩,
        ⟨10495, true, false, [], [79033]⟩,
        ⟨10502, false, false, [], []⟩,
        ⟨10502, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 79035], [2373, 79035], .contexts []⟩,
    ⟨[2373, 79035], [2373, 79035], .contexts []⟩,
    ⟨[79035, 3], [79035, 3], .contexts []⟩,
    ⟨[79035], [79035], .contexts []⟩,
    ⟨[2373], [2373], .contexts [
        ⟨24, false, false, [], [2373]⟩
      ]⟩,
    ⟨[79035, 5], [79035, 5], .contexts []⟩,
    ⟨[77149], [77149], .contexts [
        ⟨8495, false, false, [], []⟩
      ]⟩,
    ⟨[77149], [77149], .contexts [
        ⟨1118, true, false, [], [77149]⟩
      ]⟩,
    ⟨[79035, 5], [77149], .contexts [
        ⟨10509, false, false, [], []⟩,
        ⟨10501, true, false, [], [5]⟩,
        ⟨116, false, false, [79033], []⟩,
        ⟨117, false, false, [79033], []⟩,
        ⟨10485, false, false, [], [13]⟩,
        ⟨8494, false, false, [], []⟩,
        ⟨701, false, false, [], []⟩,
        ⟨477, false, false, [], []⟩,
        ⟨477, false, false, [], []⟩,
        ⟨10510, false, false, [], []⟩,
        ⟨10511, false, false, [], []⟩
      ]⟩,
    ⟨[79033, 9], [2009, 79033], .contexts [
        ⟨10487, false, false, [], []⟩,
        ⟨10481, true, false, [], [9]⟩,
        ⟨8493, true, false, [2006], [5, 9]⟩,
        ⟨8493, true, false, [2006], [5, 9]⟩,
        ⟨8492, true, false, [2006], [5, 9]⟩,
        ⟨8491, true, false, [2006], [5, 9]⟩,
        ⟨10485, true, false, [2006], [9, 5, 9]⟩,
        ⟨1497, false, false, [2006, 79033], []⟩,
        ⟨10486, false, false, [2006], []⟩,
        ⟨10488, false, false, [2006], []⟩,
        ⟨8497, true, false, [], [79033]⟩,
        ⟨8497, true, false, [], [79033]⟩,
        ⟨8496, true, false, [], [79033]⟩
      ]⟩,
    ⟨[2009, 79033], [2009, 79033], .contexts []⟩,
    ⟨[2009, 79033], [2009, 79033], .contexts []⟩,
    ⟨[2009, 79035], [2009, 79035], .contexts []⟩,
    ⟨[2009, 79035], [2009, 79035], .contexts []⟩,
    ⟨[79035, 9], [79035, 9], .contexts []⟩,
    ⟨[2009], [2009], .contexts [
        ⟨24, false, false, [], [2009]⟩
      ]⟩,
    ⟨[2377, 78813], [2377, 78813], .contexts []⟩,
    ⟨[2377, 78813], [2377, 78813], .contexts [
        ⟨24, true, false, [], [2377, 78813]⟩
      ]⟩,
    ⟨[79037], [79035, 15], .source 39583⟩,
    ⟨[79035, 15], [79037], .contexts [
        ⟨10522, true, false, [], []⟩
      ]⟩,
    ⟨[79037, 15], [79035], .contexts [
        ⟨10523, true, false, [], [15]⟩,
        ⟨3, false, false, [79035], []⟩,
        ⟨10500, false, false, [], []⟩
      ]⟩,
    ⟨[79037], [79037], .contexts []⟩,
    ⟨[79037], [79037], .contexts []⟩,
    ⟨[79035, 15], [79037], .contexts [
        ⟨10523, false, false, [], []⟩,
        ⟨10525, false, false, [], []⟩,
        ⟨10526, false, false, [], []⟩,
        ⟨10526, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 79037], [2373, 79037], .contexts []⟩,
    ⟨[2373, 79037], [2373, 79037], .contexts []⟩,
    ⟨[79037, 3], [2373, 79037], .contexts [
        ⟨10527, true, false, [], [3]⟩,
        ⟨34, false, false, [79035], []⟩,
        ⟨37, false, false, [79035], []⟩,
        ⟨10506, false, false, [], [15]⟩,
        ⟨10506, false, false, [], [15]⟩,
        ⟨10501, true, false, [], [3, 15]⟩,
        ⟨107, false, false, [79033], [15]⟩,
        ⟨109, false, false, [79033], [15]⟩,
        ⟨10503, false, false, [], [13, 15]⟩,
        ⟨10497, false, false, [2373], [15]⟩,
        ⟨10504, false, false, [], [15]⟩,
        ⟨10505, false, false, [], [15]⟩,
        ⟨10507, false, false, [2373], [15]⟩,
        ⟨10508, true, false, [], [79035, 15]⟩,
        ⟨10504, false, false, [], [15]⟩,
        ⟨10505, false, false, [], [15]⟩,
        ⟨10505, false, false, [], [15]⟩,
        ⟨10523, false, false, [2373], []⟩,
        ⟨10528, false, false, [], []⟩,
        ⟨10529, false, false, [], []⟩
      ]⟩,
    ⟨[79037], [79037], .contexts []⟩,
    ⟨[79037, 5], [79037, 5], .contexts []⟩,
    ⟨[77151], [77151], .contexts [
        ⟨8499, false, false, [], []⟩
      ]⟩,
    ⟨[77151], [77151], .contexts [
        ⟨1118, true, false, [], [77151]⟩
      ]⟩,
    ⟨[79037, 5], [77151], .contexts [
        ⟨10532, false, false, [], []⟩,
        ⟨10527, true, false, [], [5]⟩,
        ⟨48, false, false, [79035], []⟩,
        ⟨51, false, false, [79035], []⟩,
        ⟨10509, false, false, [], [15]⟩,
        ⟨10512, false, false, [], [15]⟩,
        ⟨701, false, false, [], [15]⟩,
        ⟨477, false, false, [], [15]⟩,
        ⟨477, false, false, [], [15]⟩,
        ⟨8498, false, false, [], []⟩,
        ⟨700, false, false, [], []⟩,
        ⟨480, false, false, [], []⟩,
        ⟨480, false, false, [], []⟩,
        ⟨10533, false, false, [], []⟩,
        ⟨10534, false, false, [], []⟩
      ]⟩,
    ⟨[2009, 79037], [2009, 79037], .contexts []⟩,
    ⟨[2009, 79037], [2009, 79037], .contexts []⟩,
    ⟨[79035, 9, 15], [2009, 79037], .contexts [
        ⟨10518, false, false, [], [15]⟩,
        ⟨10518, false, false, [], [15]⟩,
        ⟨10501, true, false, [], [9, 15]⟩,
        ⟨130, false, false, [79033], [15]⟩,
        ⟨131, false, false, [79033], [15]⟩,
        ⟨10487, false, false, [], [13, 15]⟩,
        ⟨10513, false, false, [], [13, 15]⟩,
        ⟨10514, false, false, [], [13, 15]⟩,
        ⟨10515, false, false, [], [13, 15]⟩,
        ⟨10515, false, false, [], [13, 15]⟩,
        ⟨10497, false, false, [2009], [15]⟩,
        ⟨10516, false, false, [], [15]⟩,
        ⟨10517, false, false, [], [15]⟩,
        ⟨10507, false, false, [2009], [15]⟩,
        ⟨10519, true, false, [], [79035, 15]⟩,
        ⟨10516, false, false, [], [15]⟩,
        ⟨10517, false, false, [], [15]⟩,
        ⟨10517, false, false, [], [15]⟩,
        ⟨10523, false, false, [2009], []⟩,
        ⟨10536, false, false, [], []⟩,
        ⟨10537, false, false, [], []⟩
      ]⟩,
    ⟨[79037, 9], [79037, 9], .contexts []⟩,
    ⟨[79039], [79037, 1], .source 39584⟩,
    ⟨[79037, 1], [79039], .contexts [
        ⟨10540, true, false, [], []⟩
      ]⟩,
    ⟨[79039, 1], [79037], .contexts [
        ⟨10541, true, false, [], [1]⟩,
        ⟨18, false, false, [79037], []⟩,
        ⟨10526, false, false, [], []⟩
      ]⟩,
    ⟨[79039], [79039], .contexts []⟩,
    ⟨[79039], [79039], .contexts []⟩,
    ⟨[79037, 5], [77151], .contexts [
        ⟨10532, false, false, [], []⟩,
        ⟨10535, false, false, [], []⟩,
        ⟨700, false, false, [], []⟩,
        ⟨480, false, false, [], []⟩,
        ⟨480, false, false, [], []⟩
      ]⟩,
    ⟨[77151, 1], [77153], .contexts [
        ⟨479, false, false, [], []⟩
      ]⟩,
    ⟨[79039, 5], [79039, 5], .contexts []⟩,
    ⟨[77153], [77153], .contexts [
        ⟨8540, false, false, [], []⟩
      ]⟩,
    ⟨[77153], [77153], .contexts [
        ⟨1118, true, false, [], [77153]⟩
      ]⟩,
    ⟨[79039, 5], [77153], .contexts [
        ⟨10547, false, false, [], []⟩,
        ⟨10544, true, false, [], [5]⟩,
        ⟨10544, true, false, [], [5]⟩,
        ⟨10543, true, false, [], [5]⟩,
        ⟨10541, true, false, [], [5]⟩,
        ⟨165, false, false, [79037], []⟩,
        ⟨166, false, false, [79037], []⟩,
        ⟨10545, false, false, [], [1]⟩,
        ⟨10546, false, false, [], []⟩,
        ⟨698, false, false, [], []⟩,
        ⟨484, false, false, [], []⟩,
        ⟨484, false, false, [], []⟩,
        ⟨10548, false, false, [], []⟩,
        ⟨10549, false, false, [], []⟩
      ]⟩,
    ⟨[77153, 5], [79039], .contexts [
        ⟨10550, true, false, [], [5]⟩,
        ⟨49, false, false, [79039], []⟩,
        ⟨10544, false, false, [], []⟩
      ]⟩,
    ⟨[79039, 5], [77153], .contexts [
        ⟨10550, false, false, [], []⟩
      ]⟩,
    ⟨[79039, 5], [77153], .contexts [
        ⟨10547, false, false, [], []⟩,
        ⟨10552, false, false, [], []⟩,
        ⟨698, false, false, [], []⟩,
        ⟨484, false, false, [], []⟩,
        ⟨484, false, false, [], []⟩
      ]⟩,
    ⟨[79039, 13], [79039, 13], .contexts []⟩,
    ⟨[79039], [79039], .contexts []⟩,
    ⟨[79041], [79039, 3], .source 39585⟩,
    ⟨[79039, 3], [79041], .contexts [
        ⟨10556, true, false, [], []⟩
      ]⟩,
    ⟨[79041, 3], [79039], .contexts [
        ⟨10557, true, false, [], [3]⟩,
        ⟨35, false, false, [79039], []⟩,
        ⟨10544, false, false, [], []⟩
      ]⟩,
    ⟨[79041], [79041], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 165. -/
def y322TCContextRaw165 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79041], [79041], .contexts []⟩,
    ⟨[79039, 3], [79041], .contexts [
        ⟨10557, false, false, [], []⟩,
        ⟨10559, false, false, [], []⟩,
        ⟨10560, false, false, [], []⟩,
        ⟨10560, false, false, [], []⟩
      ]⟩,
    ⟨[79039, 1], [79037], .contexts [
        ⟨10542, false, false, [], []⟩,
        ⟨10525, false, false, [], []⟩,
        ⟨10526, false, false, [], []⟩,
        ⟨10526, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 79041], [2373, 79041], .contexts []⟩,
    ⟨[2373, 79041], [2373, 79041], .contexts []⟩,
    ⟨[79041, 1], [79041, 1], .contexts []⟩,
    ⟨[79041], [79041], .contexts []⟩,
    ⟨[79041, 1], [2373, 79041], .contexts [
        ⟨10565, false, false, [], []⟩,
        ⟨10561, true, false, [], [1]⟩,
        ⟨213, false, false, [79039], []⟩,
        ⟨216, false, false, [79039], []⟩,
        ⟨10562, false, false, [], [3, 1, 3]⟩,
        ⟨10530, false, false, [], [1, 3]⟩,
        ⟨10531, false, false, [2373], [1, 3]⟩,
        ⟨10508, true, false, [], [79037, 1, 3]⟩,
        ⟨10528, false, false, [], [1, 3]⟩,
        ⟨10529, false, false, [], [1, 3]⟩,
        ⟨10529, false, false, [], [1, 3]⟩,
        ⟨10541, false, false, [2373], [3]⟩,
        ⟨10557, false, false, [2373], []⟩,
        ⟨10563, false, false, [], []⟩,
        ⟨10564, false, false, [], []⟩,
        ⟨10566, false, false, [2373], []⟩,
        ⟨10508, true, false, [], [79041]⟩
      ]⟩,
    ⟨[2021, 79039], [2021, 79039], .contexts []⟩,
    ⟨[79039, 13], [2021, 79039], .contexts [
        ⟨10554, false, false, [], []⟩,
        ⟨10554, false, false, [], []⟩,
        ⟨10551, true, false, [], [13]⟩,
        ⟨8546, true, false, [2018], [5, 13]⟩,
        ⟨8546, true, false, [2018], [5, 13]⟩,
        ⟨8545, true, false, [2018], [5, 13]⟩,
        ⟨8544, true, false, [2018], [5, 13]⟩,
        ⟨10553, true, false, [2018], [13, 5, 13]⟩,
        ⟨8416, false, false, [2018, 79039], []⟩,
        ⟨10555, false, false, [2018], []⟩,
        ⟨8553, true, false, [], [79039]⟩,
        ⟨10568, false, false, [], []⟩,
        ⟨10568, false, false, [], []⟩
      ]⟩,
    ⟨[2021, 79041], [2021, 79041], .contexts []⟩,
    ⟨[2021, 79041], [2021, 79041], .contexts []⟩,
    ⟨[79041, 13], [79041, 13], .contexts []⟩,
    ⟨[2021], [2021], .contexts [
        ⟨24, false, false, [], [2021]⟩
      ]⟩,
    ⟨[79043], [79041, 5], .source 39586⟩,
    ⟨[79041, 5], [79043], .contexts [
        ⟨10574, true, false, [], []⟩
      ]⟩,
    ⟨[79043], [79043], .contexts []⟩,
    ⟨[79043], [79043], .contexts []⟩,
    ⟨[79041, 5], [79043], .contexts [
        ⟨10575, false, false, [], []⟩,
        ⟨10576, false, false, [], []⟩,
        ⟨10577, false, false, [], []⟩,
        ⟨10577, false, false, [], []⟩
      ]⟩,
    ⟨[79041, 1], [2373, 79041], .contexts [
        ⟨10567, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 79043], [2373, 79043], .contexts []⟩,
    ⟨[2373, 79043], [2373, 79043], .contexts []⟩,
    ⟨[79043, 1], [79043, 1], .contexts []⟩,
    ⟨[79043], [79043], .contexts []⟩,
    ⟨[79043, 1], [2373, 79043], .contexts [
        ⟨10582, false, false, [], []⟩,
        ⟨10578, true, false, [], [1]⟩,
        ⟨256, false, false, [79041], []⟩,
        ⟨257, false, false, [79041], []⟩,
        ⟨10565, false, false, [], [5]⟩,
        ⟨10579, false, false, [], [5]⟩,
        ⟨10563, false, false, [], [5]⟩,
        ⟨10564, false, false, [], [5]⟩,
        ⟨10564, false, false, [], [5]⟩,
        ⟨10575, false, false, [2373], []⟩,
        ⟨10580, false, false, [], []⟩,
        ⟨10581, false, false, [], []⟩,
        ⟨10583, false, false, [2373], []⟩,
        ⟨10508, true, false, [], [79043]⟩
      ]⟩,
    ⟨[79041, 3], [79039], .contexts [
        ⟨10558, false, false, [], []⟩,
        ⟨10543, false, false, [], []⟩,
        ⟨10544, false, false, [], []⟩,
        ⟨10544, false, false, [], []⟩
      ]⟩,
    ⟨[79043, 3], [79043, 3], .contexts []⟩,
    ⟨[77157], [77157], .contexts [
        ⟨8559, false, false, [], []⟩
      ]⟩,
    ⟨[77157], [77157], .contexts [
        ⟨1118, true, false, [], [77157]⟩
      ]⟩,
    ⟨[79043, 3], [77157], .contexts [
        ⟨10586, false, false, [], []⟩,
        ⟨10578, true, false, [], [3]⟩,
        ⟨264, false, false, [79041], []⟩,
        ⟨267, false, false, [79041], []⟩,
        ⟨10585, false, false, [], [5, 3, 5]⟩,
        ⟨10552, false, false, [], [3, 5]⟩,
        ⟨698, false, false, [], [3, 5]⟩,
        ⟨484, false, false, [], [3, 5]⟩,
        ⟨484, false, false, [], [3, 5]⟩,
        ⟨8548, false, false, [], [5]⟩,
        ⟨696, false, false, [], [5]⟩,
        ⟨487, false, false, [], [5]⟩,
        ⟨487, false, false, [], [5]⟩,
        ⟨8556, false, false, [], []⟩,
        ⟨694, false, false, [], []⟩,
        ⟨490, false, false, [], []⟩,
        ⟨490, false, false, [], []⟩,
        ⟨10587, false, false, [], []⟩,
        ⟨10588, false, false, [], []⟩
      ]⟩,
    ⟨[79041, 13], [2021, 79041], .contexts [
        ⟨10572, false, false, [], []⟩,
        ⟨10572, false, false, [], []⟩,
        ⟨10561, true, false, [], [13]⟩,
        ⟨238, false, false, [79039], []⟩,
        ⟨239, false, false, [79039], []⟩,
        ⟨10569, false, false, [], [3]⟩,
        ⟨10557, false, false, [2021], []⟩,
        ⟨10570, false, false, [], []⟩,
        ⟨10571, false, false, [], []⟩,
        ⟨10566, false, false, [2021], []⟩,
        ⟨10573, true, false, [], [79041]⟩,
        ⟨10570, false, false, [], []⟩,
        ⟨10571, false, false, [], []⟩,
        ⟨10571, false, false, [], []⟩
      ]⟩,
    ⟨[2021, 79043], [2021, 79043], .contexts []⟩,
    ⟨[2021, 79043], [2021, 79043], .contexts []⟩,
    ⟨[2021, 79043], [2021, 79043], .contexts []⟩,
    ⟨[79043, 13], [79043, 13], .contexts []⟩,
    ⟨[79043, 1], [2373, 79043], .contexts [
        ⟨10584, false, false, [], []⟩
      ]⟩,
    ⟨[79043, 1], [2373, 79043], .contexts [
        ⟨10582, false, false, [], []⟩,
        ⟨10595, false, false, [], []⟩,
        ⟨10580, false, false, [], []⟩,
        ⟨10581, false, false, [], []⟩,
        ⟨10581, false, false, [], []⟩
      ]⟩,
    ⟨[79043, 3], [77157], .contexts [
        ⟨10586, false, false, [], []⟩,
        ⟨10589, false, false, [], []⟩,
        ⟨694, false, false, [], []⟩,
        ⟨490, false, false, [], []⟩,
        ⟨490, false, false, [], []⟩
      ]⟩,
    ⟨[77157, 1], [77159], .contexts [
        ⟨489, false, false, [], []⟩
      ]⟩,
    ⟨[77159, 3], [77159, 3], .contexts []⟩,
    ⟨[77159], [77159], .contexts []⟩,
    ⟨[77159, 3], [2375, 77159], .contexts [
        ⟨10599, false, false, [], []⟩,
        ⟨489, true, false, [], [3]⟩,
        ⟨10589, true, false, [], [1, 3]⟩,
        ⟨10596, true, false, [2372], [3, 1, 3]⟩,
        ⟨852, false, false, [2372, 79043], []⟩,
        ⟨853, false, false, [2372, 79043], []⟩,
        ⟨10597, false, false, [2372], [1]⟩,
        ⟨10598, false, false, [2372], []⟩,
        ⟨691, false, false, [2372], []⟩,
        ⟨494, false, false, [2372], []⟩,
        ⟨494, false, false, [2372], []⟩,
        ⟨10600, false, false, [2372], []⟩,
        ⟨9683, true, false, [], [77159]⟩
      ]⟩,
    ⟨[2375, 77159], [2375, 77159], .contexts []⟩,
    ⟨[77159, 3], [2375, 77159], .contexts [
        ⟨10599, false, false, [], []⟩,
        ⟨10601, false, false, [], []⟩,
        ⟨10602, false, false, [], []⟩,
        ⟨10602, false, false, [], []⟩
      ]⟩,
    ⟨[77159, 9], [77161], .contexts [
        ⟨493, false, false, [], []⟩
      ]⟩,
    ⟨[77161, 3], [77161, 3], .contexts []⟩,
    ⟨[77161], [77161], .contexts []⟩,
    ⟨[77161, 3], [2373, 77161], .contexts [
        ⟨10605, false, false, [], []⟩,
        ⟨493, true, false, [], [3]⟩,
        ⟨10603, true, false, [2374], [9, 3]⟩,
        ⟨1010, false, false, [2374, 77159], []⟩,
        ⟨77, false, false, [2374, 77159], []⟩,
        ⟨10604, false, false, [2374], []⟩,
        ⟨689, false, false, [2374], []⟩,
        ⟨497, false, false, [2374], []⟩,
        ⟨497, false, false, [2374], []⟩,
        ⟨10606, false, false, [2374], []⟩,
        ⟨10495, true, false, [], [77161]⟩
      ]⟩,
    ⟨[2373, 77161], [2373, 77161], .contexts []⟩,
    ⟨[2373, 77161], [2373, 77161], .contexts []⟩,
    ⟨[77161, 3], [2373, 77161], .contexts [
        ⟨10605, false, false, [], []⟩,
        ⟨10607, false, false, [], []⟩,
        ⟨10608, false, false, [], []⟩,
        ⟨10609, false, false, [], []⟩,
        ⟨10609, false, false, [], []⟩
      ]⟩,
    ⟨[77161, 11], [77163], .contexts [
        ⟨496, false, false, [], []⟩
      ]⟩,
    ⟨[77161, 11], [77163], .contexts [
        ⟨10611, false, false, [], []⟩,
        ⟨687, false, false, [], []⟩,
        ⟨500, false, false, [], []⟩,
        ⟨500, false, false, [], []⟩
      ]⟩,
    ⟨[77163], [77163], .contexts []⟩,
    ⟨[77163, 3], [2375, 77163], .contexts [
        ⟨496, true, false, [], [3]⟩,
        ⟨10610, true, false, [2372], [11, 3]⟩,
        ⟨976, false, false, [2372, 77161], []⟩,
        ⟨91, false, false, [2372, 77161], []⟩,
        ⟨10612, false, false, [2372], []⟩,
        ⟨10613, false, false, [2372], []⟩,
        ⟨9683, true, false, [], [77163]⟩
      ]⟩,
    ⟨[79045], [79043, 9], .source 39587⟩,
    ⟨[79043, 9], [79045], .contexts [
        ⟨10615, true, false, [], []⟩
      ]⟩,
    ⟨[79045, 9], [79043], .contexts [
        ⟨10616, true, false, [], [9]⟩,
        ⟨76, false, false, [79043], []⟩,
        ⟨10577, false, false, [], []⟩
      ]⟩,
    ⟨[79043, 9], [79045], .contexts [
        ⟨10616, false, false, [], []⟩
      ]⟩,
    ⟨[79045], [79045], .contexts []⟩,
    ⟨[79045], [79045], .contexts []⟩,
    ⟨[2021, 79045], [2021, 79045], .contexts []⟩,
    ⟨[2021, 79045], [2021, 79045], .contexts []⟩,
    ⟨[2021, 79045], [2021, 79045], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 166. -/
def y322TCContextRaw166 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79045, 13], [79045, 13], .contexts []⟩,
    ⟨[79045, 13], [2021, 79045], .contexts [
        ⟨10624, false, false, [], []⟩,
        ⟨10620, true, false, [], [13]⟩,
        ⟨10620, true, false, [], [13]⟩,
        ⟨10619, true, false, [], [13]⟩,
        ⟨10618, true, false, [], [13]⟩,
        ⟨315, false, false, [79043], []⟩,
        ⟨316, false, false, [79043], []⟩,
        ⟨10594, false, false, [], [9]⟩,
        ⟨10594, false, false, [], [9]⟩,
        ⟨10578, true, false, [], [13, 9]⟩,
        ⟨283, false, false, [79041], [9]⟩,
        ⟨284, false, false, [79041], [9]⟩,
        ⟨10590, false, false, [], [5, 9]⟩,
        ⟨10575, false, false, [2021], [9]⟩,
        ⟨10591, false, false, [], [9]⟩,
        ⟨10592, false, false, [], [9]⟩,
        ⟨10593, false, false, [], [9]⟩,
        ⟨10583, false, false, [2021], [9]⟩,
        ⟨10573, true, false, [], [79043, 9]⟩,
        ⟨10591, false, false, [], [9]⟩,
        ⟨10593, false, false, [], [9]⟩,
        ⟨10593, false, false, [], [9]⟩,
        ⟨10616, false, false, [2021], []⟩,
        ⟨10621, false, false, [], []⟩,
        ⟨10622, false, false, [], []⟩,
        ⟨10623, false, false, [], []⟩
      ]⟩,
    ⟨[79045], [79045], .contexts []⟩,
    ⟨[79045, 13], [2021, 79045], .contexts [
        ⟨10625, false, false, [], []⟩,
        ⟨10626, false, false, [2021], []⟩,
        ⟨10573, true, false, [], [79045]⟩
      ]⟩,
    ⟨[79047], [79045, 11], .source 39588⟩,
    ⟨[79045, 11], [79047], .contexts [
        ⟨10628, true, false, [], []⟩
      ]⟩,
    ⟨[79045, 11], [79047], .contexts [
        ⟨10629, false, false, [], []⟩
      ]⟩,
    ⟨[79045, 11], [79047], .contexts [
        ⟨10630, false, false, [], []⟩
      ]⟩,
    ⟨[79047], [79047], .contexts []⟩,
    ⟨[79047], [79047], .contexts []⟩,
    ⟨[2021, 79047], [2021, 79047], .contexts []⟩,
    ⟨[2021, 79047], [2021, 79047], .contexts []⟩,
    ⟨[2021, 79047], [2021, 79047], .contexts []⟩,
    ⟨[79047], [79047], .contexts []⟩,
    ⟨[79049], [79047, 1], .source 39589⟩,
    ⟨[79047, 1], [79049], .contexts [
        ⟨10638, true, false, [], []⟩
      ]⟩,
    ⟨[79049, 1], [79047], .contexts [
        ⟨10639, true, false, [], [1]⟩,
        ⟨18, false, false, [79047], []⟩,
        ⟨10633, false, false, [], []⟩
      ]⟩,
    ⟨[79051], [79049, 13], .source 39590⟩,
    ⟨[79049, 13], [79051], .contexts [
        ⟨10641, true, false, [], []⟩
      ]⟩,
    ⟨[79051], [79051], .contexts []⟩,
    ⟨[79049, 13], [79051], .contexts [
        ⟨10642, false, false, [], []⟩,
        ⟨10643, false, false, [], []⟩,
        ⟨10643, false, false, [], []⟩
      ]⟩,
    ⟨[2021, 79049], [2021, 79049], .contexts []⟩,
    ⟨[2021, 79049], [2021, 79049], .contexts []⟩,
    ⟨[79049, 1, 13, 1], [2021, 79049], .contexts [
        ⟨10640, false, false, [], [13, 1]⟩,
        ⟨10632, false, false, [], [13, 1]⟩,
        ⟨10633, false, false, [], [13, 1]⟩,
        ⟨10633, false, false, [], [13, 1]⟩,
        ⟨10633, true, false, [], [13, 1]⟩,
        ⟨10633, true, false, [], [13, 1]⟩,
        ⟨10632, true, false, [], [13, 1]⟩,
        ⟨10631, true, false, [], [13, 1]⟩,
        ⟨352, false, false, [79045], [1]⟩,
        ⟨353, false, false, [79045], [1]⟩,
        ⟨10624, false, false, [], [11, 1]⟩,
        ⟨10627, false, false, [], [11, 1]⟩,
        ⟨10621, false, false, [], [11, 1]⟩,
        ⟨10623, false, false, [], [11, 1]⟩,
        ⟨10623, false, false, [], [11, 1]⟩,
        ⟨10629, false, false, [2021], [1]⟩,
        ⟨10634, false, false, [], [1]⟩,
        ⟨10635, false, false, [], [1]⟩,
        ⟨10636, false, false, [], [1]⟩,
        ⟨10637, false, false, [2021], [1]⟩,
        ⟨10573, true, false, [], [79047, 1]⟩,
        ⟨10634, false, false, [], [1]⟩,
        ⟨10636, false, false, [], [1]⟩,
        ⟨10636, false, false, [], [1]⟩,
        ⟨10639, false, false, [2021], []⟩,
        ⟨10645, false, false, [], []⟩,
        ⟨10646, false, false, [], []⟩
      ]⟩,
    ⟨[2021, 79049], [2021, 79049], .contexts []⟩,
    ⟨[2021, 79051], [2021, 79051], .contexts []⟩,
    ⟨[2021, 79051], [2021, 79051], .contexts []⟩,
    ⟨[2021, 79051], [2021, 79051], .contexts []⟩,
    ⟨[79051, 1], [79051, 1], .contexts []⟩,
    ⟨[79051], [79051], .contexts []⟩,
    ⟨[79053], [79051, 15], .source 39591⟩,
    ⟨[79051, 15], [79053], .contexts [
        ⟨10654, true, false, [], []⟩
      ]⟩,
    ⟨[79051, 15], [79053], .contexts [
        ⟨10655, false, false, [], []⟩
      ]⟩,
    ⟨[79053], [79053], .contexts []⟩,
    ⟨[79053], [79053], .contexts []⟩,
    ⟨[79051, 15], [79053], .contexts [
        ⟨10656, false, false, [], []⟩,
        ⟨10657, false, false, [], []⟩,
        ⟨10658, false, false, [], []⟩,
        ⟨10658, false, false, [], []⟩
      ]⟩,
    ⟨[2021, 79053], [2021, 79053], .contexts []⟩,
    ⟨[2021, 79053], [2021, 79053], .contexts []⟩,
    ⟨[79053, 1], [2021, 79053], .contexts [
        ⟨10659, true, false, [], [1]⟩,
        ⟨17, false, false, [79051], []⟩,
        ⟨21, false, false, [79051], []⟩,
        ⟨10652, false, false, [], [15]⟩,
        ⟨10652, false, false, [], [15]⟩,
        ⟨10644, true, false, [], [1, 15]⟩,
        ⟨387, false, false, [79049], [15]⟩,
        ⟨390, false, false, [79049], [15]⟩,
        ⟨10647, false, false, [], [13, 15]⟩,
        ⟨10648, false, false, [], [13, 15]⟩,
        ⟨10642, false, false, [2021], [15]⟩,
        ⟨10649, false, false, [], [15]⟩,
        ⟨10650, false, false, [], [15]⟩,
        ⟨10651, false, false, [], [15]⟩,
        ⟨10653, false, false, [2021], [15]⟩,
        ⟨10573, true, false, [], [79051, 15]⟩,
        ⟨10649, false, false, [], [15]⟩,
        ⟨10651, false, false, [], [15]⟩,
        ⟨10651, false, false, [], [15]⟩,
        ⟨10655, false, false, [2021], []⟩,
        ⟨10660, false, false, [], []⟩,
        ⟨10661, false, false, [], []⟩
      ]⟩,
    ⟨[79053], [79053], .contexts []⟩,
    ⟨[79053, 1], [2021, 79053], .contexts [
        ⟨10662, false, false, [], []⟩,
        ⟨10663, false, false, [2021], []⟩,
        ⟨10573, true, false, [], [79053]⟩
      ]⟩,
    ⟨[79055], [79053, 3], .source 39592⟩,
    ⟨[79053, 3], [79055], .contexts [
        ⟨10665, true, false, [], []⟩
      ]⟩,
    ⟨[79057], [79055, 5], .source 39593⟩,
    ⟨[79055, 5], [79057], .contexts [
        ⟨10667, true, false, [], []⟩
      ]⟩,
    ⟨[79055], [79055], .contexts []⟩,
    ⟨[79059], [79057, 1], .source 39594⟩,
    ⟨[79057, 1], [79059], .contexts [
        ⟨10670, true, false, [], []⟩
      ]⟩,
    ⟨[79057], [79057], .contexts []⟩,
    ⟨[79059, 1], [79057], .contexts [
        ⟨10671, true, false, [], [1]⟩,
        ⟨18, false, false, [79057], []⟩,
        ⟨10672, false, false, [], []⟩
      ]⟩,
    ⟨[79061], [79059, 9], .source 39595⟩,
    ⟨[79059], [79059], .contexts []⟩,
    ⟨[79063], [79061, 11], .source 39596⟩,
    ⟨[79061], [79061], .contexts []⟩,
    ⟨[79065], [79063, 1], .source 39597⟩,
    ⟨[79063], [79063], .contexts []⟩,
    ⟨[79067], [79065, 13], .source 39598⟩,
    ⟨[79065], [79065], .contexts []⟩,
    ⟨[79069], [79067, 15], .source 39599⟩,
    ⟨[79067], [79067], .contexts []⟩,
    ⟨[79071], [79069, 1], .source 39600⟩,
    ⟨[79069], [79069], .contexts []⟩,
    ⟨[79073], [79071, 3], .source 39601⟩,
    ⟨[79071], [79071], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 167. -/
def y322TCContextRaw167 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79075], [79073, 5], .source 39602⟩,
    ⟨[79073], [79073], .contexts []⟩,
    ⟨[79077], [79075, 1], .source 39603⟩,
    ⟨[79075], [79075], .contexts []⟩,
    ⟨[79079], [79077, 9], .source 39604⟩,
    ⟨[79077], [79077], .contexts []⟩,
    ⟨[79081], [79079, 11], .source 39605⟩,
    ⟨[79079], [79079], .contexts []⟩,
    ⟨[79083], [79081, 1], .source 39606⟩,
    ⟨[79081], [79081], .contexts []⟩,
    ⟨[79085], [79083, 13], .source 39607⟩,
    ⟨[79083], [79083], .contexts []⟩,
    ⟨[79087], [79085, 15], .source 39608⟩,
    ⟨[79085], [79085], .contexts []⟩,
    ⟨[79089], [79087, 1], .source 39609⟩,
    ⟨[79087], [79087], .contexts []⟩,
    ⟨[79091], [79089, 3], .source 39610⟩,
    ⟨[79089], [79089], .contexts []⟩,
    ⟨[79093], [79091, 5], .source 39611⟩,
    ⟨[79091], [79091], .contexts []⟩,
    ⟨[79095], [79093, 1], .source 39612⟩,
    ⟨[79093], [79093], .contexts []⟩,
    ⟨[79097], [79095, 9], .source 39613⟩,
    ⟨[79095], [79095], .contexts []⟩,
    ⟨[79099], [79097, 11], .source 39614⟩,
    ⟨[79097], [79097], .contexts []⟩,
    ⟨[79101], [79099, 1], .source 39615⟩,
    ⟨[79099], [79099], .contexts []⟩,
    ⟨[79103], [79101, 13], .source 39616⟩,
    ⟨[79101], [79101], .contexts []⟩,
    ⟨[79105], [79103, 15], .source 39617⟩,
    ⟨[79103], [79103], .contexts []⟩,
    ⟨[79107], [79105, 1], .source 39618⟩,
    ⟨[79105], [79105], .contexts []⟩,
    ⟨[79109], [79107, 3], .source 39619⟩,
    ⟨[79107], [79107], .contexts []⟩,
    ⟨[79111], [79109, 5], .source 39620⟩,
    ⟨[79109], [79109], .contexts []⟩,
    ⟨[79113], [79111, 1], .source 39621⟩,
    ⟨[79111], [79111], .contexts []⟩,
    ⟨[79115], [79113, 9], .source 39622⟩,
    ⟨[79113], [79113], .contexts []⟩,
    ⟨[79117], [79115, 11], .source 39623⟩,
    ⟨[79115], [79115], .contexts []⟩,
    ⟨[79119], [79117, 1], .source 39624⟩,
    ⟨[79117], [79117], .contexts []⟩,
    ⟨[79121], [79119, 13], .source 39625⟩,
    ⟨[79119], [79119], .contexts []⟩,
    ⟨[79123], [79121, 15], .source 39626⟩,
    ⟨[79121], [79121], .contexts []⟩,
    ⟨[79125], [79123, 1], .source 39627⟩,
    ⟨[79123], [79123], .contexts []⟩,
    ⟨[79127], [79125, 3], .source 39628⟩,
    ⟨[79125], [79125], .contexts []⟩,
    ⟨[79129], [79127, 5], .source 39629⟩,
    ⟨[79127], [79127], .contexts []⟩,
    ⟨[79131], [79129, 1], .source 39630⟩,
    ⟨[79129], [79129], .contexts []⟩,
    ⟨[79133], [79131, 9], .source 39631⟩,
    ⟨[79131], [79131], .contexts []⟩,
    ⟨[79135], [79133, 11], .source 39632⟩,
    ⟨[79133], [79133], .contexts []⟩,
    ⟨[79137], [79135, 1], .source 39633⟩,
    ⟨[79135], [79135], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 168. -/
def y322TCContextRaw168 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79139], [79137, 13], .source 39634⟩,
    ⟨[79137], [79137], .contexts []⟩,
    ⟨[79141], [79139, 15], .source 39635⟩,
    ⟨[79139], [79139], .contexts []⟩,
    ⟨[79143], [79141, 1], .source 39636⟩,
    ⟨[79141], [79141], .contexts []⟩,
    ⟨[79143, 1], [79141], .contexts [
        ⟨10756, false, false, [], [1]⟩,
        ⟨18, false, false, [79141], []⟩,
        ⟨10757, false, false, [], []⟩
      ]⟩,
    ⟨[79145], [79143, 3], .source 39637⟩,
    ⟨[79143], [79143], .contexts []⟩,
    ⟨[79145, 3], [79143], .contexts [
        ⟨10759, false, false, [], [3]⟩,
        ⟨35, false, false, [79143], []⟩,
        ⟨10760, false, false, [], []⟩
      ]⟩,
    ⟨[79147], [79145, 5], .source 39638⟩,
    ⟨[79145, 5], [79147], .contexts [
        ⟨10762, true, false, [], []⟩
      ]⟩,
    ⟨[79145], [79145], .contexts []⟩,
    ⟨[79147, 5], [79145], .contexts [
        ⟨10763, true, false, [], [5]⟩,
        ⟨49, false, false, [79145], []⟩,
        ⟨10764, false, false, [], []⟩
      ]⟩,
    ⟨[79149], [79147, 1], .source 39639⟩,
    ⟨[79147], [79147], .contexts []⟩,
    ⟨[79149, 1], [79147], .contexts [
        ⟨10766, false, false, [], [1]⟩,
        ⟨18, false, false, [79147], []⟩,
        ⟨10767, false, false, [], []⟩
      ]⟩,
    ⟨[79151], [79149, 9], .source 39640⟩,
    ⟨[79149], [79149], .contexts []⟩,
    ⟨[79151, 9], [79149], .contexts [
        ⟨10769, false, false, [], [9]⟩,
        ⟨76, false, false, [79149], []⟩,
        ⟨10770, false, false, [], []⟩
      ]⟩,
    ⟨[79153], [79151, 11], .source 39641⟩,
    ⟨[79151], [79151], .contexts []⟩,
    ⟨[79153, 11], [79151], .contexts [
        ⟨10772, false, false, [], [11]⟩,
        ⟨90, false, false, [79151], []⟩,
        ⟨10773, false, false, [], []⟩
      ]⟩,
    ⟨[79155], [79153, 1], .source 39642⟩,
    ⟨[79153, 1], [79155], .contexts [
        ⟨10775, true, false, [], []⟩
      ]⟩,
    ⟨[79153], [79153], .contexts []⟩,
    ⟨[79155, 1], [79153], .contexts [
        ⟨10776, true, false, [], [1]⟩,
        ⟨18, false, false, [79153], []⟩,
        ⟨10777, false, false, [], []⟩
      ]⟩,
    ⟨[79157], [79155, 13], .source 39643⟩,
    ⟨[79155], [79155], .contexts []⟩,
    ⟨[79157, 13], [79155], .contexts [
        ⟨10779, false, false, [], [13]⟩,
        ⟨98, false, false, [79155], []⟩,
        ⟨10780, false, false, [], []⟩
      ]⟩,
    ⟨[79159], [79157, 15], .source 39644⟩,
    ⟨[79157], [79157], .contexts []⟩,
    ⟨[79159, 15], [79157], .contexts [
        ⟨10782, false, false, [], [15]⟩,
        ⟨3, false, false, [79157], []⟩,
        ⟨10783, false, false, [], []⟩
      ]⟩,
    ⟨[79161], [79159, 1], .source 39645⟩,
    ⟨[79159], [79159], .contexts []⟩,
    ⟨[79161, 1], [79159], .contexts [
        ⟨10785, false, false, [], [1]⟩,
        ⟨18, false, false, [79159], []⟩,
        ⟨10786, false, false, [], []⟩
      ]⟩,
    ⟨[79163], [79161, 3], .source 39646⟩,
    ⟨[79161], [79161], .contexts []⟩,
    ⟨[79163, 3], [79161], .contexts [
        ⟨10788, false, false, [], [3]⟩,
        ⟨35, false, false, [79161], []⟩,
        ⟨10789, false, false, [], []⟩
      ]⟩,
    ⟨[79165], [79163, 5], .source 39647⟩,
    ⟨[79163, 5], [79165], .contexts [
        ⟨10791, true, false, [], []⟩
      ]⟩,
    ⟨[79163], [79163], .contexts []⟩,
    ⟨[79165, 5], [79163], .contexts [
        ⟨10792, true, false, [], [5]⟩,
        ⟨49, false, false, [79163], []⟩,
        ⟨10793, false, false, [], []⟩
      ]⟩,
    ⟨[79167], [79165, 1], .source 39648⟩,
    ⟨[79165, 1], [79167], .contexts [
        ⟨10795, true, false, [], []⟩
      ]⟩,
    ⟨[79165], [79165], .contexts []⟩,
    ⟨[79167, 1], [79165], .contexts [
        ⟨10796, true, false, [], [1]⟩,
        ⟨18, false, false, [79165], []⟩,
        ⟨10797, false, false, [], []⟩
      ]⟩,
    ⟨[79169], [79167, 9], .source 39649⟩,
    ⟨[79167], [79167], .contexts []⟩,
    ⟨[79169, 9], [79167], .contexts [
        ⟨10799, false, false, [], [9]⟩,
        ⟨76, false, false, [79167], []⟩,
        ⟨10800, false, false, [], []⟩
      ]⟩,
    ⟨[79171], [79169, 11], .source 39650⟩,
    ⟨[79169], [79169], .contexts []⟩,
    ⟨[79171, 11], [79169], .contexts [
        ⟨10802, false, false, [], [11]⟩,
        ⟨90, false, false, [79169], []⟩,
        ⟨10803, false, false, [], []⟩
      ]⟩,
    ⟨[79173], [79171, 1], .source 39651⟩,
    ⟨[79171, 1], [79173], .contexts [
        ⟨10805, true, false, [], []⟩
      ]⟩,
    ⟨[79171], [79171], .contexts []⟩,
    ⟨[79173, 1], [79171], .contexts [
        ⟨10806, true, false, [], [1]⟩,
        ⟨18, false, false, [79171], []⟩,
        ⟨10807, false, false, [], []⟩
      ]⟩,
    ⟨[79173], [79173], .contexts []⟩,
    ⟨[79173], [79173], .contexts []⟩,
    ⟨[79169], [79169], .contexts []⟩,
    ⟨[79171, 11], [79169], .contexts [
        ⟨10804, false, false, [], []⟩,
        ⟨10811, false, false, [], []⟩,
        ⟨10803, false, false, [], []⟩,
        ⟨10803, false, false, [], []⟩
      ]⟩,
    ⟨[79169, 9], [79167], .contexts [
        ⟨10801, false, false, [], []⟩
      ]⟩,
    ⟨[79167], [79167], .contexts []⟩,
    ⟨[79165], [79165], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 169. -/
def y322TCContextRaw169 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79165, 5], [79163], .contexts [
        ⟨10794, false, false, [], []⟩
      ]⟩,
    ⟨[79163], [79163], .contexts []⟩,
    ⟨[79161], [79161], .contexts []⟩,
    ⟨[79161, 1], [79159], .contexts [
        ⟨10787, false, false, [], []⟩
      ]⟩,
    ⟨[79159], [79159], .contexts []⟩,
    ⟨[79171, 11, 9, 1, 5, 3, 1], [79159], .contexts [
        ⟨10812, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨10813, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10814, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10800, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10800, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10798, false, false, [], [5, 3, 1]⟩,
        ⟨10815, false, false, [], [5, 3, 1]⟩,
        ⟨10797, false, false, [], [5, 3, 1]⟩,
        ⟨10797, false, false, [], [5, 3, 1]⟩,
        ⟨10816, false, false, [], [3, 1]⟩,
        ⟨10817, false, false, [], [3, 1]⟩,
        ⟨10793, false, false, [], [3, 1]⟩,
        ⟨10793, false, false, [], [3, 1]⟩,
        ⟨10790, false, false, [], [1]⟩,
        ⟨10818, false, false, [], [1]⟩,
        ⟨10789, false, false, [], [1]⟩,
        ⟨10789, false, false, [], [1]⟩,
        ⟨10819, false, false, [], []⟩,
        ⟨10820, false, false, [], []⟩,
        ⟨10786, false, false, [], []⟩,
        ⟨10786, false, false, [], []⟩
      ]⟩,
    ⟨[79157], [79157], .contexts []⟩,
    ⟨[79155], [79155], .contexts []⟩,
    ⟨[79151, 9], [79149], .contexts [
        ⟨10771, false, false, [], []⟩
      ]⟩,
    ⟨[79149], [79149], .contexts []⟩,
    ⟨[79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [79149], .contexts [
        ⟨10821, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨10784, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10822, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10783, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10783, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10781, false, false, [], [1, 11, 9]⟩,
        ⟨10823, false, false, [], [1, 11, 9]⟩,
        ⟨10780, false, false, [], [1, 11, 9]⟩,
        ⟨10780, false, false, [], [1, 11, 9]⟩,
        ⟨10778, false, false, [], [11, 9]⟩,
        ⟨10777, false, false, [], [11, 9]⟩,
        ⟨10777, false, false, [], [11, 9]⟩,
        ⟨10774, false, false, [], [9]⟩,
        ⟨10773, false, false, [], [9]⟩,
        ⟨10773, false, false, [], [9]⟩,
        ⟨10824, false, false, [], []⟩,
        ⟨10825, false, false, [], []⟩,
        ⟨10770, false, false, [], []⟩,
        ⟨10770, false, false, [], []⟩
      ]⟩,
    ⟨[79149, 1], [79147], .contexts [
        ⟨10768, false, false, [], []⟩
      ]⟩,
    ⟨[79147], [79147], .contexts []⟩,
    ⟨[79145, 3], [79143], .contexts [
        ⟨10761, false, false, [], []⟩
      ]⟩,
    ⟨[79143], [79143], .contexts []⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [79139], .contexts [
        ⟨10826, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨10827, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10828, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10767, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10767, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10765, false, false, [], [3, 1, 15]⟩,
        ⟨10764, false, false, [], [3, 1, 15]⟩,
        ⟨10764, false, false, [], [3, 1, 15]⟩,
        ⟨10829, false, false, [], [1, 15]⟩,
        ⟨10830, false, false, [], [1, 15]⟩,
        ⟨10760, false, false, [], [1, 15]⟩,
        ⟨10760, false, false, [], [1, 15]⟩,
        ⟨10758, false, false, [], [15]⟩,
        ⟨10757, false, false, [], [15]⟩,
        ⟨10757, false, false, [], [15]⟩,
        ⟨10754, false, false, [], [15]⟩,
        ⟨3, false, false, [79139], []⟩,
        ⟨10755, false, false, [], []⟩,
        ⟨10755, false, false, [], []⟩,
        ⟨10755, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [79131], .contexts [
        ⟨10831, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10752, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [79137], [1, 11, 9]⟩,
        ⟨10753, false, false, [], [1, 11, 9]⟩,
        ⟨10753, false, false, [], [1, 11, 9]⟩,
        ⟨10753, false, false, [], [1, 11, 9]⟩,
        ⟨10750, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [79135], [11, 9]⟩,
        ⟨10751, false, false, [], [11, 9]⟩,
        ⟨10751, false, false, [], [11, 9]⟩,
        ⟨10751, false, false, [], [11, 9]⟩,
        ⟨10748, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [79133], [9]⟩,
        ⟨10749, false, false, [], [9]⟩,
        ⟨10749, false, false, [], [9]⟩,
        ⟨10749, false, false, [], [9]⟩,
        ⟨10746, false, false, [], [9]⟩,
        ⟨76, false, false, [79131], []⟩,
        ⟨10747, false, false, [], []⟩,
        ⟨10747, false, false, [], []⟩,
        ⟨10747, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [79123], .contexts [
        ⟨10832, false, false, [], [1, 5, 3, 1]⟩,
        ⟨10744, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [79129], [5, 3, 1]⟩,
        ⟨10745, false, false, [], [5, 3, 1]⟩,
        ⟨10745, false, false, [], [5, 3, 1]⟩,
        ⟨10745, false, false, [], [5, 3, 1]⟩,
        ⟨10742, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [79127], [3, 1]⟩,
        ⟨10743, false, false, [], [3, 1]⟩,
        ⟨10743, false, false, [], [3, 1]⟩,
        ⟨10743, false, false, [], [3, 1]⟩,
        ⟨10740, false, false, [], [3, 1]⟩,
        ⟨35, false, false, [79125], [1]⟩,
        ⟨10741, false, false, [], [1]⟩,
        ⟨10741, false, false, [], [1]⟩,
        ⟨10741, false, false, [], [1]⟩,
        ⟨10738, false, false, [], [1]⟩,
        ⟨18, false, false, [79123], []⟩,
        ⟨10739, false, false, [], []⟩,
        ⟨10739, false, false, [], []⟩,
        ⟨10739, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [79115], .contexts [
        ⟨10833, false, false, [], [15, 13, 1, 11]⟩,
        ⟨10736, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [79121], [13, 1, 11]⟩,
        ⟨10737, false, false, [], [13, 1, 11]⟩,
        ⟨10737, false, false, [], [13, 1, 11]⟩,
        ⟨10737, false, false, [], [13, 1, 11]⟩,
        ⟨10734, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [79119], [1, 11]⟩,
        ⟨10735, false, false, [], [1, 11]⟩,
        ⟨10735, false, false, [], [1, 11]⟩,
        ⟨10735, false, false, [], [1, 11]⟩,
        ⟨10732, false, false, [], [1, 11]⟩,
        ⟨18, false, false, [79117], [11]⟩,
        ⟨10733, false, false, [], [11]⟩,
        ⟨10733, false, false, [], [11]⟩,
        ⟨10733, false, false, [], [11]⟩,
        ⟨10730, false, false, [], [11]⟩,
        ⟨90, false, false, [79115], []⟩,
        ⟨10731, false, false, [], []⟩,
        ⟨10731, false, false, [], []⟩,
        ⟨10731, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [79107], .contexts [
        ⟨10834, false, false, [], [9, 1, 5, 3]⟩,
        ⟨10728, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [79113], [1, 5, 3]⟩,
        ⟨10729, false, false, [], [1, 5, 3]⟩,
        ⟨10729, false, false, [], [1, 5, 3]⟩,
        ⟨10729, false, false, [], [1, 5, 3]⟩,
        ⟨10726, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [79111], [5, 3]⟩,
        ⟨10727, false, false, [], [5, 3]⟩,
        ⟨10727, false, false, [], [5, 3]⟩,
        ⟨10727, false, false, [], [5, 3]⟩,
        ⟨10724, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [79109], [3]⟩,
        ⟨10725, false, false, [], [3]⟩,
        ⟨10725, false, false, [], [3]⟩,
        ⟨10725, false, false, [], [3]⟩,
        ⟨10722, false, false, [], [3]⟩,
        ⟨35, false, false, [79107], []⟩,
        ⟨10723, false, false, [], []⟩,
        ⟨10723, false, false, [], []⟩,
        ⟨10723, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [79099], .contexts [
        ⟨10835, false, false, [], [1, 15, 13, 1]⟩,
        ⟨10720, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [79105], [15, 13, 1]⟩,
        ⟨10721, false, false, [], [15, 13, 1]⟩,
        ⟨10721, false, false, [], [15, 13, 1]⟩,
        ⟨10721, false, false, [], [15, 13, 1]⟩,
        ⟨10718, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [79103], [13, 1]⟩,
        ⟨10719, false, false, [], [13, 1]⟩,
        ⟨10719, false, false, [], [13, 1]⟩,
        ⟨10719, false, false, [], [13, 1]⟩,
        ⟨10716, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [79101], [1]⟩,
        ⟨10717, false, false, [], [1]⟩,
        ⟨10717, false, false, [], [1]⟩,
        ⟨10717, false, false, [], [1]⟩,
        ⟨10714, false, false, [], [1]⟩,
        ⟨18, false, false, [79099], []⟩,
        ⟨10715, false, false, [], []⟩,
        ⟨10715, false, false, [], []⟩,
        ⟨10715, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [79091], .contexts [
        ⟨10836, false, false, [], [11, 9, 1, 5]⟩,
        ⟨10712, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [79097], [9, 1, 5]⟩,
        ⟨10713, false, false, [], [9, 1, 5]⟩,
        ⟨10713, false, false, [], [9, 1, 5]⟩,
        ⟨10713, false, false, [], [9, 1, 5]⟩,
        ⟨10710, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [79095], [1, 5]⟩,
        ⟨10711, false, false, [], [1, 5]⟩,
        ⟨10711, false, false, [], [1, 5]⟩,
        ⟨10711, false, false, [], [1, 5]⟩,
        ⟨10708, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [79093], [5]⟩,
        ⟨10709, false, false, [], [5]⟩,
        ⟨10709, false, false, [], [5]⟩,
        ⟨10709, false, false, [], [5]⟩,
        ⟨10706, false, false, [], [5]⟩,
        ⟨49, false, false, [79091], []⟩,
        ⟨10707, false, false, [], []⟩,
        ⟨10707, false, false, [], []⟩,
        ⟨10707, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [79083], .contexts [
        ⟨10837, false, false, [], [3, 1, 15, 13]⟩,
        ⟨10704, false, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [79089], [1, 15, 13]⟩,
        ⟨10705, false, false, [], [1, 15, 13]⟩,
        ⟨10705, false, false, [], [1, 15, 13]⟩,
        ⟨10705, false, false, [], [1, 15, 13]⟩,
        ⟨10702, false, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [79087], [15, 13]⟩,
        ⟨10703, false, false, [], [15, 13]⟩,
        ⟨10703, false, false, [], [15, 13]⟩,
        ⟨10703, false, false, [], [15, 13]⟩,
        ⟨10700, false, false, [], [15, 13]⟩,
        ⟨3, false, false, [79085], [13]⟩,
        ⟨10701, false, false, [], [13]⟩,
        ⟨10701, false, false, [], [13]⟩,
        ⟨10701, false, false, [], [13]⟩,
        ⟨10698, false, false, [], [13]⟩,
        ⟨98, false, false, [79083], []⟩,
        ⟨10699, false, false, [], []⟩,
        ⟨10699, false, false, [], []⟩,
        ⟨10699, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [79075], .contexts [
        ⟨10838, false, false, [], [1, 11, 9, 1]⟩,
        ⟨10696, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [79081], [11, 9, 1]⟩,
        ⟨10697, false, false, [], [11, 9, 1]⟩,
        ⟨10697, false, false, [], [11, 9, 1]⟩,
        ⟨10697, false, false, [], [11, 9, 1]⟩,
        ⟨10694, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [79079], [9, 1]⟩,
        ⟨10695, false, false, [], [9, 1]⟩,
        ⟨10695, false, false, [], [9, 1]⟩,
        ⟨10695, false, false, [], [9, 1]⟩,
        ⟨10692, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [79077], [1]⟩,
        ⟨10693, false, false, [], [1]⟩,
        ⟨10693, false, false, [], [1]⟩,
        ⟨10693, false, false, [], [1]⟩,
        ⟨10690, false, false, [], [1]⟩,
        ⟨18, false, false, [79075], []⟩,
        ⟨10691, false, false, [], []⟩,
        ⟨10691, false, false, [], []⟩,
        ⟨10691, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [79067], .contexts [
        ⟨10839, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10688, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [79073], [3, 1, 15]⟩,
        ⟨10689, false, false, [], [3, 1, 15]⟩,
        ⟨10689, false, false, [], [3, 1, 15]⟩,
        ⟨10689, false, false, [], [3, 1, 15]⟩,
        ⟨10686, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [79071], [1, 15]⟩,
        ⟨10687, false, false, [], [1, 15]⟩,
        ⟨10687, false, false, [], [1, 15]⟩,
        ⟨10687, false, false, [], [1, 15]⟩,
        ⟨10684, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [79069], [15]⟩,
        ⟨10685, false, false, [], [15]⟩,
        ⟨10685, false, false, [], [15]⟩,
        ⟨10685, false, false, [], [15]⟩,
        ⟨10682, false, false, [], [15]⟩,
        ⟨3, false, false, [79067], []⟩,
        ⟨10683, false, false, [], []⟩,
        ⟨10683, false, false, [], []⟩,
        ⟨10683, false, false, [], []⟩
      ]⟩,
    ⟨[79059], [79059], .contexts []⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [79059], .contexts [
        ⟨10840, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10680, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [79065], [1, 11, 9]⟩,
        ⟨10681, false, false, [], [1, 11, 9]⟩,
        ⟨10681, false, false, [], [1, 11, 9]⟩,
        ⟨10681, false, false, [], [1, 11, 9]⟩,
        ⟨10678, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [79063], [11, 9]⟩,
        ⟨10679, false, false, [], [11, 9]⟩,
        ⟨10679, false, false, [], [11, 9]⟩,
        ⟨10679, false, false, [], [11, 9]⟩,
        ⟨10676, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [79061], [9]⟩,
        ⟨10677, false, false, [], [9]⟩,
        ⟨10677, false, false, [], [9]⟩,
        ⟨10677, false, false, [], [9]⟩,
        ⟨10674, false, false, [], [9]⟩,
        ⟨76, false, false, [79059], []⟩,
        ⟨10675, false, false, [], []⟩,
        ⟨10841, false, false, [], []⟩,
        ⟨10675, false, false, [], []⟩,
        ⟨10675, false, false, [], []⟩
      ]⟩,
    ⟨[79055], [79055], .contexts []⟩,
    ⟨[79055, 3], [79053], .contexts [
        ⟨10666, true, false, [], [3]⟩,
        ⟨35, false, false, [79053], []⟩,
        ⟨10658, false, false, [], []⟩
      ]⟩,
    ⟨[79053, 1], [2021, 79053], .contexts [
        ⟨10664, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [2021, 79051], .contexts [
        ⟨10842, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨10673, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10672, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10672, false, false, [], [5, 3, 1, 15]⟩,
        ⟨10668, true, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [79055], [3, 1, 15]⟩,
        ⟨10669, false, false, [], [3, 1, 15]⟩,
        ⟨10843, false, false, [], [3, 1, 15]⟩,
        ⟨10669, false, false, [], [3, 1, 15]⟩,
        ⟨10669, false, false, [], [3, 1, 15]⟩,
        ⟨10844, false, false, [], [1, 15]⟩,
        ⟨10657, false, false, [], [1, 15]⟩,
        ⟨10658, false, false, [], [1, 15]⟩,
        ⟨10658, false, false, [], [1, 15]⟩,
        ⟨10845, false, false, [], [15]⟩,
        ⟨10660, false, false, [], [15]⟩,
        ⟨10661, false, false, [], [15]⟩,
        ⟨10661, false, false, [], [15]⟩,
        ⟨10655, true, false, [2021], [15]⟩,
        ⟨3, false, false, [2021, 79051], []⟩,
        ⟨10643, false, false, [2021], []⟩,
        ⟨10649, false, false, [], []⟩,
        ⟨10650, false, false, [], []⟩,
        ⟨10651, false, false, [], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [2021, 79043], .contexts [
        ⟨10846, false, false, [], [13, 1, 11, 9]⟩,
        ⟨10642, true, false, [2021], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [2021, 79049], [1, 11, 9]⟩,
        ⟨10645, false, false, [], [1, 11, 9]⟩,
        ⟨10646, false, false, [], [1, 11, 9]⟩,
        ⟨10648, false, false, [], [1, 11, 9]⟩,
        ⟨10640, false, false, [2021], [11, 9]⟩,
        ⟨10634, false, false, [], [11, 9]⟩,
        ⟨10635, false, false, [], [11, 9]⟩,
        ⟨10636, false, false, [], [11, 9]⟩,
        ⟨10629, true, false, [2021], [11, 9]⟩,
        ⟨90, false, false, [2021, 79045], [9]⟩,
        ⟨10620, false, false, [2021], [9]⟩,
        ⟨10621, false, false, [], [9]⟩,
        ⟨10622, false, false, [], [9]⟩,
        ⟨10623, false, false, [], [9]⟩,
        ⟨10617, false, false, [2021], []⟩,
        ⟨10591, false, false, [], []⟩,
        ⟨10592, false, false, [], []⟩,
        ⟨10593, false, false, [], []⟩
      ]⟩,
    ⟨[2593], [2021, 2373], .source 1361⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [2593, 79035], .contexts [
        ⟨10847, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨10584, false, false, [2021], [5, 3, 1, 15]⟩,
        ⟨10848, true, false, [], [79043, 5, 3, 1, 15]⟩,
        ⟨10575, true, false, [2593], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [2593, 79041], [3, 1, 15]⟩,
        ⟨10560, false, false, [2593], [3, 1, 15]⟩,
        ⟨10558, false, false, [2593], [1, 15]⟩,
        ⟨10542, false, false, [2593], [15]⟩,
        ⟨10524, false, false, [2593], []⟩
      ]⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [2593, 77137], .contexts [
        ⟨10849, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨10498, false, false, [2593], [1, 11, 9, 1]⟩,
        ⟨10473, false, false, [2593], [11, 9, 1]⟩,
        ⟨10464, false, false, [2593], [9, 1]⟩,
        ⟨9636, false, false, [2593], [1]⟩,
        ⟨9101, false, false, [2593], []⟩
      ]⟩,
    ⟨[2595], [2593, 315], .source 1362⟩,
    ⟨[2597], [2595, 1887], .source 1363⟩,
    ⟨[2599], [2597, 1997], .source 1364⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [2599, 78555], .contexts [
        ⟨10850, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨456, false, false, [2593], [3, 1, 15, 13]⟩,
        ⟨2021, false, false, [2593], [1, 15, 13]⟩,
        ⟨10851, true, false, [], [77139, 1, 15, 13]⟩,
        ⟨459, false, false, [2595], [15, 13]⟩,
        ⟨8408, false, false, [2595], [13]⟩,
        ⟨10852, true, false, [], [78555, 13]⟩,
        ⟨8421, false, false, [2597], []⟩,
        ⟨10853, true, false, [], [78555]⟩
      ]⟩,
    ⟨[2601], [2599, 1899], .source 1365⟩,
    ⟨[2603], [2601, 2453], .source 1366⟩,
    ⟨[2605], [2603, 2473], .source 1367⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [2605, 78985], .contexts [
        ⟨10854, false, false, [], [1, 11, 9]⟩,
        ⟨8394, false, false, [2599], [11, 9]⟩,
        ⟨9786, false, false, [2599], [11, 9]⟩,
        ⟨10855, true, false, [], [78421, 11, 9]⟩,
        ⟨10127, false, false, [2601], [9]⟩,
        ⟨10856, true, false, [], [78985, 9]⟩,
        ⟨10121, false, false, [2603, 2470], [78985, 9]⟩,
        ⟨10110, false, false, [2603, 2470, 2469], [78985, 9]⟩,
        ⟨98, true, false, [2603, 2470, 2469, 2450, 78985], [9]⟩,
        ⟨10109, false, false, [2603, 2470, 2469, 2450], [13, 9]⟩,
        ⟨10120, false, false, [2603, 2470], [78417, 13, 9]⟩,
        ⟨7704, true, false, [2603, 2470, 2451], [13, 9]⟩,
        ⟨10112, true, false, [2603, 2470], [9, 13, 9]⟩,
        ⟨10122, false, false, [2603, 2470, 78985], []⟩,
        ⟨10113, false, false, [2603, 2470], []⟩,
        ⟨10114, false, false, [2603, 2470], []⟩,
        ⟨10124, true, false, [2603], [78985]⟩,
        ⟨10124, true, false, [2603], [78985]⟩,
        ⟨10123, true, false, [2603], [78985]⟩,
        ⟨10857, true, false, [], [78985]⟩
      ]⟩,
    ⟨[2607], [2605, 2465], .source 1368⟩,
    ⟨[2609], [2607, 749], .source 1369⟩,
    ⟨[2611], [2609, 1281], .source 1370⟩,
    ⟨[
      79171, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [2611, 78727], .contexts [
        ⟨10858, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨10052, false, false, [2605], [5, 3, 1, 15]⟩,
        ⟨10133, false, false, [2605], [3, 1, 15]⟩,
        ⟨10859, true, false, [], [77583, 3, 1, 15]⟩,
        ⟨3472, false, false, [2607], [1, 15]⟩,
        ⟨10860, true, false, [], [77327, 1, 15]⟩,
        ⟨1307, false, false, [2609], [15]⟩,
        ⟨9262, true, false, [2609, 1278], [15]⟩,
        ⟨3, false, false, [2609, 1278, 78727], []⟩,
        ⟨5677, true, false, [2609], [78727]⟩,
        ⟨10861, true, false, [], [78727]⟩
      ]⟩,
    ⟨[79173, 13], [79173, 13], .contexts []⟩,
    ⟨[2611], [2611], .contexts []⟩,
    ⟨[2611], [2611], .contexts []⟩,
    ⟨[79173, 13], [2611, 78727], .contexts [
        ⟨10863, false, false, [], []⟩,
        ⟨10810, true, false, [], [13]⟩,
        ⟨10810, true, false, [], [13]⟩,
        ⟨10809, true, false, [], [13]⟩,
        ⟨10806, true, false, [], [13]⟩,
        ⟨10098, false, false, [79171], []⟩,
        ⟨10106, false, false, [79171], []⟩,
        ⟨10862, false, false, [], []⟩,
        ⟨9266, false, false, [2611], []⟩,
        ⟨10865, true, false, [], [78727]⟩,
        ⟨10864, true, false, [], [78727]⟩,
        ⟨24, true, false, [], [2611, 78727]⟩
      ]⟩,
    ⟨[2613], [2610], .source 1371⟩,
    ⟨[2611, 78727], [2611, 78727], .contexts []⟩,
    ⟨[2611, 78727], [2611, 78727], .contexts []⟩,
    ⟨[79173, 13], [2611, 78727], .contexts [
        ⟨10863, false, false, [], []⟩,
        ⟨10866, false, false, [], []⟩,
        ⟨10868, false, false, [], []⟩,
        ⟨10869, false, false, [], []⟩,
        ⟨10869, false, false, [], []⟩
      ]⟩,
    ⟨[2615], [2611, 2195], .source 1372⟩,
    ⟨[2615, 78239], [2615, 78239], .contexts []⟩,
    ⟨[2615, 78239], [2615, 78239], .contexts []⟩,
    ⟨[79171, 13], [79171, 13], .contexts []⟩,
    ⟨[2615], [2615], .contexts []⟩,
    ⟨[2615], [2615], .contexts []⟩,
    ⟨[79171, 13], [2615, 78239], .contexts [
        ⟨10874, false, false, [], []⟩,
        ⟨10807, true, false, [], [13]⟩,
        ⟨10807, true, false, [], [13]⟩,
        ⟨10808, true, false, [], [13]⟩,
        ⟨189, false, false, [79173], []⟩,
        ⟨192, false, false, [79173], []⟩,
        ⟨10870, false, false, [], [1, 13, 1]⟩,
        ⟨9251, false, false, [2611], [13, 1]⟩,
        ⟨10871, true, false, [], [78243, 13, 1]⟩,
        ⟨6512, false, false, [2615], [1]⟩,
        ⟨6508, false, false, [2615], []⟩,
        ⟨10872, false, false, [], []⟩,
        ⟨10873, false, false, [], []⟩,
        ⟨6698, false, false, [2615], []⟩,
        ⟨10876, true, false, [], [78239]⟩,
        ⟨10875, true, false, [], [78239]⟩,
        ⟨24, true, false, [], [2615, 78239]⟩
      ]⟩,
    ⟨[2617], [2614], .source 1373⟩,
    ⟨[79173], [79173], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 170. -/
def y322TCContextRaw170 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79173], [79173], .contexts []⟩,
    ⟨[2631], [2611, 2219], .source 1380⟩,
    ⟨[2633], [2631, 765], .source 1381⟩,
    ⟨[2635], [2632], .source 1382⟩,
    ⟨[2632], [2632], .contexts []⟩,
    ⟨[79173, 9], [2633, 77611], .contexts [
        ⟨10883, false, false, [2634], [79173, 9]⟩,
        ⟨10884, false, false, [2634], [79173, 9]⟩,
        ⟨10884, false, false, [2634], [79173, 9]⟩,
        ⟨10880, true, false, [2634, 2632], [9]⟩,
        ⟨10879, true, false, [2634, 2632], [9]⟩,
        ⟨10122, true, false, [2634, 2632, 79173], [9]⟩,
        ⟨10870, false, false, [2634, 2632], [9, 13, 9, 9]⟩,
        ⟨9270, false, false, [2634, 2632, 2611], [13, 9, 9]⟩,
        ⟨10881, true, false, [2634, 2632], [77497, 13, 9, 9]⟩,
        ⟨3679, false, false, [2634, 2632, 2631], [9, 9]⟩,
        ⟨10882, true, false, [2634, 2632], [77611, 9, 9]⟩,
        ⟨76, false, false, [2634, 77611], []⟩,
        ⟨10883, false, true, [], [77611]⟩
      ]⟩,
    ⟨[2637], [2611, 539], .source 1383⟩,
    ⟨[77871, 11], [77871, 11], .contexts []⟩,
    ⟨[2639], [2636], .source 1384⟩,
    ⟨[2636], [2636], .contexts []⟩,
    ⟨[77871, 11], [2639, 79173], .contexts [
        ⟨10887, false, false, [], []⟩,
        ⟨10886, false, false, [2636], [77871, 11]⟩,
        ⟨8351, true, false, [2636, 2611], [11]⟩,
        ⟨9247, true, false, [2636, 2611], [13, 11]⟩,
        ⟨10870, true, false, [2636], [11, 13, 11]⟩,
        ⟨9287, false, false, [2636, 79173], []⟩,
        ⟨10879, false, false, [2636], []⟩,
        ⟨10880, false, false, [2636], []⟩,
        ⟨10889, true, false, [], [79173]⟩,
        ⟨10889, true, false, [], [79173]⟩,
        ⟨10888, true, false, [], [79173]⟩
      ]⟩,
    ⟨[2641], [2611, 1279], .source 1385⟩,
    ⟨[2643], [2641, 719], .source 1386⟩,
    ⟨[2643, 77453, 15], [79173], .contexts [
        ⟨10892, false, false, [], [77453, 15]⟩,
        ⟨3402, true, false, [2641], [15]⟩,
        ⟨1315, true, false, [2641], [13, 15]⟩,
        ⟨1311, true, false, [2641], [15, 13, 15]⟩,
        ⟨10891, false, false, [], [77329, 13, 15, 13, 15]⟩,
        ⟨9262, true, false, [2611], [13, 15, 13, 15]⟩,
        ⟨10870, true, false, [], [15, 13, 15, 13, 15]⟩,
        ⟨147, false, false, [79173], []⟩,
        ⟨10879, false, false, [], []⟩
      ]⟩,
    ⟨[77453, 15], [77453, 15], .contexts []⟩,
    ⟨[2645], [2642], .source 1387⟩,
    ⟨[2645], [2645], .contexts []⟩,
    ⟨[2645], [2642], .contexts [
        ⟨10895, false, false, [], []⟩
      ]⟩,
    ⟨[2642], [2642], .contexts []⟩,
    ⟨[77453, 15], [2645, 79173], .contexts [
        ⟨10894, false, false, [], []⟩,
        ⟨10893, false, false, [2642], []⟩,
        ⟨10880, false, false, [2642], []⟩,
        ⟨10898, true, false, [], [79173]⟩,
        ⟨10898, true, false, [], [79173]⟩,
        ⟨10897, true, false, [], [79173]⟩,
        ⟨10896, true, false, [], [79173]⟩
      ]⟩,
    ⟨[2643], [2644], .contexts [
        ⟨10895, true, true, [], []⟩
      ]⟩,
    ⟨[78237, 13], [78237, 13], .contexts []⟩,
    ⟨[79169], [79169], .contexts []⟩,
    ⟨[2614], [2614], .contexts []⟩,
    ⟨[78237, 13], [2617, 79169], .contexts [
        ⟨10901, false, false, [], []⟩,
        ⟨6504, true, false, [], [13]⟩,
        ⟨10873, true, false, [2614], [11, 13]⟩,
        ⟨10873, true, false, [2614], [11, 13]⟩,
        ⟨10872, true, false, [2614], [11, 13]⟩,
        ⟨10877, true, false, [2614], [11, 13]⟩,
        ⟨10874, true, false, [2614], [11, 13]⟩,
        ⟨1624, false, false, [2614, 79171], []⟩,
        ⟨91, false, false, [2614, 79171], []⟩,
        ⟨10812, false, false, [2614], []⟩,
        ⟨10902, false, false, [2614], []⟩,
        ⟨10903, true, false, [], [79169]⟩,
        ⟨10903, true, false, [], [79169]⟩,
        ⟨10878, true, false, [], [79169]⟩
      ]⟩,
    ⟨[2615], [2616], .contexts [
        ⟨10878, true, true, [], []⟩
      ]⟩,
    ⟨[79169, 13], [2615, 78237], .contexts [
        ⟨10904, true, false, [2616], [13]⟩,
        ⟨98, false, false, [2616, 78237], []⟩,
        ⟨10905, true, false, [], [78237]⟩
      ]⟩,
    ⟨[2639, 79173], [2639, 79173], .contexts []⟩,
    ⟨[79169, 1], [79169, 1], .contexts []⟩,
    ⟨[2638], [2638], .contexts []⟩,
    ⟨[79169, 1], [2637, 77871], .contexts [
        ⟨10908, false, false, [], []⟩,
        ⟨10804, true, false, [], [1]⟩,
        ⟨10808, true, false, [], [11, 1]⟩,
        ⟨10907, true, false, [2638], [1, 11, 1]⟩,
        ⟨10907, true, false, [2638], [1, 11, 1]⟩,
        ⟨10890, true, false, [2638], [1, 11, 1]⟩,
        ⟨10887, true, false, [2638], [1, 11, 1]⟩,
        ⟨1068, false, false, [2638, 77871], []⟩,
        ⟨4959, false, false, [2638], []⟩,
        ⟨10909, true, false, [], [77871]⟩,
        ⟨10909, true, false, [], [77871]⟩,
        ⟨10888, false, true, [], [77871]⟩
      ]⟩,
    ⟨[2645, 79173], [2645, 79173], .contexts []⟩,
    ⟨[2645, 79171], [2645, 79171], .contexts []⟩,
    ⟨[2644], [2644], .contexts []⟩,
    ⟨[77449], [2645, 79171], .contexts [
        ⟨2746, true, false, [], []⟩,
        ⟨10900, false, false, [2642], [77451, 15]⟩,
        ⟨10913, false, false, [2642], [77451, 15]⟩,
        ⟨10913, false, false, [2642], [77451, 15]⟩,
        ⟨2744, true, false, [2642, 2644], [15]⟩,
        ⟨3421, true, false, [2642, 2644], [15]⟩,
        ⟨3423, true, false, [2642, 2644], [15]⟩,
        ⟨2778, true, false, [2642, 2644, 77453], [15]⟩,
        ⟨10894, false, false, [2642, 2644], [1, 15, 15]⟩,
        ⟨10899, false, false, [2642, 2644], [1, 15, 15]⟩,
        ⟨10911, false, false, [2642, 2644], [1, 15, 15]⟩,
        ⟨10911, false, false, [2642, 2644], [1, 15, 15]⟩,
        ⟨10808, false, false, [2642], [15, 15]⟩,
        ⟨10912, false, false, [2642, 2644], [15, 15]⟩,
        ⟨3, false, false, [2642, 79171], []⟩,
        ⟨10895, true, false, [], [79171]⟩
      ]⟩,
    ⟨[79171], [2643, 77449], .contexts [
        ⟨10896, false, false, [2644], [79171]⟩,
        ⟨10912, true, false, [2644], []⟩,
        ⟨10914, true, false, [2644], []⟩,
        ⟨10900, true, false, [], [77449]⟩
      ]⟩,
    ⟨[2645], [2642], .contexts [
        ⟨10897, false, false, [], []⟩,
        ⟨10898, false, false, [], []⟩,
        ⟨10898, false, false, [], []⟩
      ]⟩,
    ⟨[77449, 11], [2645, 79169], .contexts [
        ⟨10915, true, false, [2642], [11]⟩,
        ⟨10804, false, false, [2642], []⟩,
        ⟨10811, false, false, [2642], []⟩,
        ⟨10916, true, false, [], [79169]⟩
      ]⟩,
    ⟨[79171], [2643, 77449], .contexts [
        ⟨10915, false, false, [], []⟩
      ]⟩,
    ⟨[2657], [2645, 2615], .source 1393⟩,
    ⟨[2659], [2656], .source 1394⟩,
    ⟨[78239], [2659, 77447], .contexts [
        ⟨10919, false, false, [2656], [78239]⟩,
        ⟨10895, false, false, [2656], [2615, 78239]⟩,
        ⟨10875, false, false, [2656, 2642], [78239]⟩,
        ⟨10876, false, false, [2656, 2642], [78239]⟩,
        ⟨10872, true, false, [2656, 2642], []⟩,
        ⟨10877, true, false, [2656, 2642], []⟩,
        ⟨10918, false, false, [2656, 2642], [13]⟩,
        ⟨2248, false, false, [2656], []⟩,
        ⟨10920, true, false, [], [77447]⟩
      ]⟩,
    ⟨[2657], [2658], .contexts [
        ⟨10920, true, true, [], []⟩
      ]⟩,
    ⟨[2657], [2658], .contexts [
        ⟨10922, false, false, [], []⟩
      ]⟩,
    ⟨[2658], [2658], .contexts []⟩,
    ⟨[2657], [2658], .contexts [
        ⟨10923, false, false, [], []⟩,
        ⟨10924, false, false, [], []⟩,
        ⟨10924, false, false, [], []⟩
      ]⟩,
    ⟨[77447, 11], [2657, 78237], .contexts [
        ⟨10921, true, false, [2658], [11]⟩,
        ⟨6504, false, false, [2658], []⟩,
        ⟨6549, false, false, [2658], []⟩,
        ⟨10925, true, false, [], [78237]⟩
      ]⟩,
    ⟨[2659, 77447], [2659, 77447], .contexts []⟩,
    ⟨[78239], [2659, 77447], .contexts [
        ⟨10921, false, false, [], []⟩,
        ⟨10927, false, false, [], []⟩
      ]⟩,
    ⟨[2661], [2657, 2205], .source 1395⟩,
    ⟨[2661], [2658, 2205], .contexts [
        ⟨10929, false, false, [], []⟩,
        ⟨10922, false, false, [], [2205]⟩
      ]⟩,
    ⟨[77447, 5], [2661, 78849], .contexts [
        ⟨10921, true, false, [2658], [5]⟩,
        ⟨9882, false, false, [2658], []⟩,
        ⟨10930, true, false, [], [78849]⟩
      ]⟩,
    ⟨[2659, 77445], [2659, 77445], .contexts []⟩,
    ⟨[78241], [2659, 77445], .contexts [
        ⟨10923, false, false, [2656], [78241]⟩,
        ⟨24, false, false, [2656, 2658], [78241]⟩,
        ⟨6545, true, false, [2656, 2658], []⟩,
        ⟨6506, true, false, [2656, 2658], []⟩,
        ⟨10928, false, false, [2656, 2658], [1]⟩,
        ⟨2244, false, false, [2656], []⟩,
        ⟨10932, false, false, [2656, 2658], []⟩,
        ⟨10920, true, false, [], [77445]⟩
      ]⟩,
    ⟨[77445, 13], [2657, 78243], .contexts [
        ⟨10933, true, false, [2658], [13]⟩,
        ⟨6510, false, false, [2658], []⟩,
        ⟨6543, false, false, [2658], []⟩,
        ⟨10925, true, false, [], [78243]⟩
      ]⟩,
    ⟨[78241], [2659, 77445], .contexts [
        ⟨10933, false, false, [], []⟩,
        ⟨10932, false, false, [], []⟩
      ]⟩,
    ⟨[2663], [2657, 1463], .source 1396⟩,
    ⟨[2665], [2663, 1895], .source 1397⟩,
    ⟨[77445, 5], [2661, 78847], .contexts [
        ⟨10933, true, false, [2658], [5]⟩,
        ⟨9865, false, false, [2658], []⟩,
        ⟨10930, true, false, [], [78847]⟩
      ]⟩,
    ⟨[77449, 3, 11], [535, 2645, 79169], .contexts [
        ⟨2747, false, false, [], [11]⟩,
        ⟨2747, false, false, [], [11]⟩,
        ⟨2252, true, false, [], [3, 11]⟩,
        ⟨2741, true, false, [532], [15, 3, 11]⟩,
        ⟨2745, true, false, [532], [15, 3, 11]⟩,
        ⟨900, false, false, [532, 77451], [11]⟩,
        ⟨20, false, false, [532, 77451], [11]⟩,
        ⟨2746, false, false, [532], [11]⟩,
        ⟨2748, false, false, [532], [11]⟩,
        ⟨2750, true, false, [], [77449, 11]⟩,
        ⟨2750, true, false, [], [77449, 11]⟩,
        ⟨2749, true, false, [], [77449, 11]⟩,
        ⟨2751, false, false, [], [11]⟩,
        ⟨2751, false, false, [], [11]⟩,
        ⟨10917, false, false, [535], []⟩
      ]⟩,
    ⟨[2667], [535, 2645], .source 1398⟩,
    ⟨[2645, 79169], [2645, 79169], .contexts []⟩,
    ⟨[77449, 11], [2645, 79169], .contexts [
        ⟨10917, false, false, [], []⟩,
        ⟨10941, false, false, [], []⟩,
        ⟨10941, false, false, [], []⟩
      ]⟩,
    ⟨[77449, 10], [77449, 11], .contexts [
        ⟨91, false, false, [77449], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 171. -/
def y322TCContextRaw171 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79169, 3], [79169, 3], .contexts []⟩,
    ⟨[2669], [2666], .source 1399⟩,
    ⟨[2671], [2669, 2645], .source 1400⟩,
    ⟨[2617, 79169], [2617, 79169], .contexts []⟩,
    ⟨[2616], [2616], .contexts []⟩,
    ⟨[79167, 13], [2615, 78235], .contexts [
        ⟨10801, true, false, [], [13]⟩,
        ⟨10947, true, false, [2616], [9, 13]⟩,
        ⟨10947, true, false, [2616], [9, 13]⟩,
        ⟨10904, true, false, [2616], [9, 13]⟩,
        ⟨10901, true, false, [2616], [9, 13]⟩,
        ⟨1650, false, false, [2616, 78237], []⟩,
        ⟨6722, false, false, [2616], []⟩,
        ⟨6721, false, false, [2616], []⟩,
        ⟨6724, false, false, [2616], []⟩,
        ⟨10948, true, false, [], [78235]⟩,
        ⟨10948, true, false, [], [78235]⟩,
        ⟨10905, true, false, [], [78235]⟩
      ]⟩,
    ⟨[2673], [1015, 2645], .source 1401⟩,
    ⟨[2675], [2672], .source 1402⟩,
    ⟨[2677], [2675, 2645], .source 1403⟩,
    ⟨[2637, 77871], [2637, 77871], .contexts []⟩,
    ⟨[79169, 1], [2637, 77871], .contexts [
        ⟨10908, false, false, [], []⟩,
        ⟨10910, false, false, [], []⟩,
        ⟨10953, false, false, [], []⟩,
        ⟨10953, false, false, [], []⟩
      ]⟩,
    ⟨[2679], [2637, 2235], .source 1404⟩,
    ⟨[79169], [79169], .contexts []⟩,
    ⟨[77619, 5], [77619, 5], .contexts []⟩,
    ⟨[2681], [2678], .source 1405⟩,
    ⟨[2678], [2678], .contexts []⟩,
    ⟨[2683], [2637, 1059], .source 1406⟩,
    ⟨[2685], [2683, 2639], .source 1407⟩,
    ⟨[2685, 79165], [2685, 79165], .contexts []⟩,
    ⟨[2685, 79165], [2685, 79165], .contexts []⟩,
    ⟨[2685, 79165, 9], [79169], .contexts [
        ⟨10963, true, false, [], [9]⟩,
        ⟨10962, true, false, [], [9]⟩,
        ⟨10798, true, false, [2685], [9]⟩,
        ⟨10801, true, false, [2685], [1, 9]⟩,
        ⟨10961, false, false, [], [79169, 9, 1, 9]⟩,
        ⟨10888, false, false, [2683], [79169, 9, 1, 9]⟩,
        ⟨18, true, false, [2683, 2636, 79169], [9, 1, 9]⟩,
        ⟨10910, false, false, [2683, 2636], [1, 9, 1, 9]⟩,
        ⟨10960, false, false, [], [77871, 1, 9, 1, 9]⟩,
        ⟨4960, true, false, [2637], [1, 9, 1, 9]⟩,
        ⟨10954, true, false, [], [9, 1, 9, 1, 9]⟩,
        ⟨7565, false, false, [79169], []⟩,
        ⟨10956, false, false, [], []⟩
      ]⟩,
    ⟨[79165, 9], [79165, 9], .contexts []⟩,
    ⟨[2687], [2684], .source 1408⟩,
    ⟨[2684], [2684], .contexts []⟩,
    ⟨[79165, 9], [2687, 79169], .contexts [
        ⟨10965, false, false, [], []⟩,
        ⟨10964, false, false, [2684], []⟩,
        ⟨10902, false, false, [2684], []⟩,
        ⟨10967, true, false, [], [79169]⟩,
        ⟨10967, true, false, [], [79169]⟩,
        ⟨10966, true, false, [], [79169]⟩
      ]⟩,
    ⟨[79169, 9], [79167], .contexts [
        ⟨10813, false, false, [], []⟩
      ]⟩,
    ⟨[79167], [2685, 79165], .contexts [
        ⟨10800, true, false, [], []⟩,
        ⟨10800, true, false, [], []⟩,
        ⟨10814, true, false, [], []⟩,
        ⟨10969, true, false, [], []⟩,
        ⟨10968, true, false, [2686], [9]⟩,
        ⟨76, false, false, [2686, 79165], []⟩,
        ⟨10966, false, true, [], [79165]⟩,
        ⟨10962, false, false, [], []⟩
      ]⟩,
    ⟨[2689], [2687, 2615], .source 1409⟩,
    ⟨[79165, 13], [2689, 78235], .contexts [
        ⟨10970, true, false, [2684], [13]⟩,
        ⟨10949, false, false, [2684], []⟩,
        ⟨10966, true, false, [], [2615, 78235]⟩,
        ⟨10971, true, false, [], [78235]⟩
      ]⟩,
    ⟨[79167], [2685, 79165], .contexts [
        ⟨10970, false, false, [], []⟩,
        ⟨10963, false, false, [], []⟩
      ]⟩,
    ⟨[2691], [2687, 2677], .source 1410⟩,
    ⟨[2693], [2691, 2685], .source 1411⟩,
    ⟨[77451, 11], [1365, 78115], .contexts [
        ⟨6151, false, false, [], []⟩
      ]⟩,
    ⟨[1365, 78115], [1365, 78115], .contexts []⟩,
    ⟨[1365, 78115], [1365, 78115], .contexts []⟩,
    ⟨[1363], [1364], .contexts [
        ⟨6150, true, true, [], []⟩
      ]⟩,
    ⟨[2695], [1363, 2645], .source 1412⟩,
    ⟨[78115, 15], [2695, 79169], .contexts [
        ⟨10978, true, false, [1364], [15]⟩,
        ⟨10978, true, false, [1364], [15]⟩,
        ⟨10977, true, false, [1364], [15]⟩,
        ⟨10976, true, false, [1364], [15]⟩,
        ⟨2255, true, false, [1364], [11, 15]⟩,
        ⟨2255, true, false, [1364], [11, 15]⟩,
        ⟨2318, true, false, [1364], [11, 15]⟩,
        ⟨2250, true, false, [1364], [11, 15]⟩,
        ⟨3495, false, false, [1364, 77449], []⟩,
        ⟨10943, false, false, [1364], []⟩,
        ⟨10942, false, false, [1364], []⟩,
        ⟨10902, false, false, [1364, 2645], []⟩,
        ⟨10979, true, false, [], [2645, 79169]⟩,
        ⟨10980, true, false, [], [79169]⟩
      ]⟩,
    ⟨[2697], [2694], .source 1413⟩,
    ⟨[79169, 15], [2697, 78115], .contexts [
        ⟨10981, true, false, [2694], [15]⟩,
        ⟨3, false, false, [2694, 78115], []⟩,
        ⟨10982, true, false, [], [78115]⟩
      ]⟩,
    ⟨[2657, 78237], [2657, 78237], .contexts []⟩,
    ⟨[2657, 78237], [2657, 78237], .contexts []⟩,
    ⟨[77447, 11], [2657, 78237], .contexts [
        ⟨10926, false, false, [], []⟩,
        ⟨10984, false, false, [], []⟩,
        ⟨10985, false, false, [], []⟩,
        ⟨10985, false, false, [], []⟩
      ]⟩,
    ⟨[77443, 1], [77443, 1], .contexts []⟩,
    ⟨[77443, 1], [2657, 78237], .contexts [
        ⟨10987, false, false, [], []⟩,
        ⟨2239, true, false, [], [1]⟩,
        ⟨2239, true, false, [], [1]⟩,
        ⟨2326, true, false, [], [1]⟩,
        ⟨2325, true, false, [], [1]⟩,
        ⟨3475, true, false, [], [11, 1]⟩,
        ⟨8090, false, false, [77447], []⟩,
        ⟨91, false, false, [77447], []⟩,
        ⟨10986, false, false, [], []⟩,
        ⟨6713, false, false, [2657], []⟩,
        ⟨24, true, false, [], [2657, 78237]⟩
      ]⟩,
    ⟨[78237, 1], [2659, 77443], .contexts [
        ⟨10988, true, false, [2656], [1]⟩,
        ⟨18, false, false, [2656, 77443], []⟩,
        ⟨10920, true, false, [], [77443]⟩
      ]⟩,
    ⟨[77447, 9], [1033, 77447], .contexts [
        ⟨4752, false, false, [], []⟩
      ]⟩,
    ⟨[1033, 77447], [1033, 77447], .contexts []⟩,
    ⟨[1033, 77447], [1033, 77447], .contexts []⟩,
    ⟨[2705], [1033, 2657], .source 1417⟩,
    ⟨[2657, 78237, 9], [2657, 78235], .contexts [
        ⟨6500, false, false, [2657], []⟩
      ]⟩,
    ⟨[2657, 78235], [2657, 78235], .contexts []⟩,
    ⟨[2657, 78235], [2657, 78235], .contexts []⟩,
    ⟨[2657, 78235], [2657, 78235], .contexts []⟩,
    ⟨[78235, 11], [78235, 11], .contexts []⟩,
    ⟨[2707], [2704], .source 1418⟩,
    ⟨[2709], [2707, 2657], .source 1419⟩,
    ⟨[2665, 77577], [2665, 77577], .contexts []⟩,
    ⟨[2665, 77575], [2665, 77575], .contexts []⟩,
    ⟨[2665, 77575], [2665, 77575], .contexts []⟩,
    ⟨[77443, 3], [77443, 3], .contexts []⟩,
    ⟨[77443, 3], [2665, 77575], .contexts [
        ⟨11004, false, false, [], []⟩,
        ⟨3494, true, false, [], [3]⟩,
        ⟨335, false, false, [77445], []⟩,
        ⟨336, false, false, [77445], []⟩,
        ⟨10933, true, false, [2658], [3, 11]⟩,
        ⟨6707, false, false, [2658], [11]⟩,
        ⟨8083, false, false, [2658, 1463], [11]⟩,
        ⟨10922, true, false, [], [1463, 1895, 77577, 11]⟩,
        ⟨10936, true, false, [], [1895, 77577, 11]⟩,
        ⟨10937, true, false, [], [77577, 11]⟩,
        ⟨11001, false, false, [], [11]⟩,
        ⟨11001, false, false, [], [11]⟩,
        ⟨3106, false, false, [2665], []⟩,
        ⟨11002, false, false, [], []⟩,
        ⟨11003, false, false, [], []⟩,
        ⟨3528, false, false, [2665], []⟩,
        ⟨24, true, false, [], [2665, 77575]⟩
      ]⟩,
    ⟨[2711], [2664], .source 1420⟩,
    ⟨[2657, 78243], [2657, 78243], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 172. -/
def y322TCContextRaw172 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2713], [2657, 2197], .source 1421⟩,
    ⟨[77443, 13], [2713, 78719], .contexts [
        ⟨3494, true, false, [], [13]⟩,
        ⟨352, false, false, [77445], []⟩,
        ⟨353, false, false, [77445], []⟩,
        ⟨10934, false, false, [], [11]⟩,
        ⟨11007, false, false, [], [11]⟩,
        ⟨11007, false, false, [], [11]⟩,
        ⟨9156, true, false, [2657, 2194], [11]⟩,
        ⟨90, false, false, [2657, 2194, 78719], []⟩,
        ⟨9157, true, false, [2657], [78719]⟩,
        ⟨11008, true, false, [], [78719]⟩,
        ⟨9168, false, false, [2713], []⟩,
        ⟨24, true, false, [], [2713, 78719]⟩
      ]⟩,
    ⟨[2671, 79169], [2671, 79169], .contexts []⟩,
    ⟨[2717], [2671, 2685], .source 1423⟩,
    ⟨[79167], [2685, 79165], .contexts [
        ⟨10973, false, false, [], []⟩
      ]⟩,
    ⟨[2717, 79165, 3], [79169, 8], .contexts [
        ⟨11011, false, false, [], [79165, 3]⟩,
        ⟨10973, true, false, [2671], [3]⟩,
        ⟨10801, true, false, [2671], [3]⟩,
        ⟨11010, true, false, [], [9, 3]⟩,
        ⟨11010, true, false, [], [9, 3]⟩,
        ⟨10946, false, false, [], [79169, 9, 3]⟩,
        ⟨10945, false, false, [], [2645, 79169, 9, 3]⟩,
        ⟨10902, true, false, [2666, 2645], [9, 3]⟩,
        ⟨10942, true, false, [2666], [9, 3]⟩,
        ⟨10943, true, false, [2666], [9, 3]⟩,
        ⟨976, true, false, [2666, 77449], [9, 3]⟩,
        ⟨10939, false, false, [2666], [3, 9, 3]⟩,
        ⟨10940, true, false, [2666], [79169, 3, 9, 3]⟩,
        ⟨10944, true, false, [], [9, 3]⟩,
        ⟨10944, true, false, [], [9, 3]⟩,
        ⟨1010, false, false, [79169], []⟩
      ]⟩,
    ⟨[79165, 3], [79165, 3], .contexts []⟩,
    ⟨[79165], [79165], .contexts []⟩,
    ⟨[2719], [2716], .source 1424⟩,
    ⟨[2721], [2719, 2685], .source 1425⟩,
    ⟨[2689, 78235], [2689, 78235], .contexts []⟩,
    ⟨[79165, 13], [2689, 78235], .contexts [
        ⟨10972, false, false, [], []⟩,
        ⟨11018, false, false, [], []⟩,
        ⟨11018, false, false, [], []⟩
      ]⟩,
    ⟨[79165, 1], [2685, 79165], .contexts [
        ⟨10796, false, false, [], []⟩,
        ⟨11012, false, false, [], []⟩,
        ⟨10963, false, false, [], []⟩,
        ⟨10963, false, false, [], []⟩
      ]⟩,
    ⟨[2723], [2685, 2689], .source 1426⟩,
    ⟨[78233, 13], [78233, 13], .contexts []⟩,
    ⟨[2725], [2688], .source 1427⟩,
    ⟨[2727], [2725, 2723], .source 1428⟩,
    ⟨[79165, 11], [2693, 79165], .contexts [
        ⟨10970, true, false, [2684], [11]⟩,
        ⟨10801, true, false, [2684], [11]⟩,
        ⟨10950, false, false, [2684, 2672], [79169, 9, 11]⟩,
        ⟨10917, true, false, [2684, 2672, 1015], [9, 11]⟩,
        ⟨4748, true, false, [2684, 2672], [11, 9, 11]⟩,
        ⟨966, false, false, [2684, 2672, 77449], []⟩,
        ⟨967, false, false, [2684, 2672, 77449], []⟩,
        ⟨10942, false, false, [2684, 2672], [9]⟩,
        ⟨10801, false, false, [2684, 2672, 2645], []⟩,
        ⟨10951, true, false, [2684], [2645, 79167]⟩,
        ⟨10952, true, false, [2684], [79167]⟩,
        ⟨10973, false, false, [2684, 2677], []⟩,
        ⟨10966, true, false, [], [2677, 2685, 79165]⟩,
        ⟨10974, true, false, [], [2685, 79165]⟩,
        ⟨10975, true, false, [], [79165]⟩
      ]⟩,
    ⟨[2693, 79165], [2693, 79165], .contexts []⟩,
    ⟨[79165, 5], [79163], .contexts [
        ⟨10816, false, false, [], []⟩
      ]⟩,
    ⟨[2729], [2692], .source 1429⟩,
    ⟨[2692], [2692], .contexts []⟩,
    ⟨[2681, 79169], [2681, 79169], .contexts []⟩,
    ⟨[77619, 5], [2681, 79169], .contexts [
        ⟨10957, false, false, [], []⟩,
        ⟨10957, false, false, [], []⟩,
        ⟨3746, true, false, [], [5]⟩,
        ⟨10955, false, false, [2678], [77617, 1, 5]⟩,
        ⟨9297, true, false, [2678, 2637], [1, 5]⟩,
        ⟨4962, true, false, [2678, 2637], [1, 5]⟩,
        ⟨10954, true, false, [2678], [5, 1, 5]⟩,
        ⟨1909, false, false, [2678, 79169], []⟩,
        ⟨10956, false, false, [2678], []⟩,
        ⟨10902, false, false, [2678], []⟩,
        ⟨10959, true, false, [], [79169]⟩,
        ⟨10959, true, false, [], [79169]⟩,
        ⟨10958, true, false, [], [79169]⟩,
        ⟨11030, false, false, [], []⟩,
        ⟨11030, false, false, [], []⟩
      ]⟩,
    ⟨[2731], [2681, 2685], .source 1430⟩,
    ⟨[2731, 79163], [2731, 79163], .contexts []⟩,
    ⟨[2733], [2730], .source 1431⟩,
    ⟨[2730], [2730], .contexts []⟩,
    ⟨[2233, 77877], [2233, 77877], .contexts []⟩,
    ⟨[2233, 77877], [2731, 79163], .contexts [
        ⟨11036, true, false, [], []⟩,
        ⟨11036, true, false, [], []⟩,
        ⟨9302, true, false, [], []⟩,
        ⟨11034, false, false, [2732], [77619, 9]⟩,
        ⟨11035, false, false, [2732], [77619, 9]⟩,
        ⟨11035, false, false, [2732], [77619, 9]⟩,
        ⟨1497, true, false, [2732, 2730, 77619], [9]⟩,
        ⟨11031, false, false, [2732, 2730], [9, 5, 9, 9]⟩,
        ⟨10801, false, false, [2732, 2730, 2681], [5, 9, 9]⟩,
        ⟨10973, false, false, [2732, 2730, 2681], [5, 9, 9]⟩,
        ⟨11032, true, false, [2732, 2730], [79165, 5, 9, 9]⟩,
        ⟨10794, false, false, [2732], [9, 9]⟩,
        ⟨11033, false, false, [2732, 2730], [9, 9]⟩,
        ⟨76, false, false, [2732, 79163], []⟩,
        ⟨11034, false, true, [], [79163]⟩
      ]⟩,
    ⟨[2735], [2235, 2731], .source 1432⟩,
    ⟨[2737], [2734], .source 1433⟩,
    ⟨[79163], [2737, 77877], .contexts [
        ⟨11038, false, false, [2734], [79163]⟩,
        ⟨9288, false, false, [2734], [2731, 79163]⟩,
        ⟨11033, true, false, [2734, 2232], []⟩,
        ⟨11037, true, false, [2734, 2232], []⟩,
        ⟨11039, true, false, [], [77877]⟩
      ]⟩,
    ⟨[2735], [2736], .contexts [
        ⟨11039, true, true, [], []⟩
      ]⟩,
    ⟨[2736], [2736], .contexts []⟩,
    ⟨[2735], [2736], .contexts [
        ⟨11041, false, false, [], []⟩,
        ⟨11042, false, false, [], []⟩,
        ⟨11042, false, false, [], []⟩
      ]⟩,
    ⟨[77877, 3], [2735, 79161], .contexts [
        ⟨11040, true, false, [2736], [3]⟩,
        ⟨10790, false, false, [2736], []⟩,
        ⟨10818, false, false, [2736], []⟩,
        ⟨11043, true, false, [], [79161]⟩
      ]⟩,
    ⟨[2737, 77877], [2737, 77877], .contexts []⟩,
    ⟨[79163], [2737, 77877], .contexts [
        ⟨11040, false, false, [], []⟩,
        ⟨11045, false, false, [], []⟩
      ]⟩,
    ⟨[2739], [2729, 2737], .source 1434⟩,
    ⟨[2741], [2735, 2739], .source 1435⟩,
    ⟨[77879], [2741, 77877], .contexts [
        ⟨4988, true, false, [], []⟩,
        ⟨11046, true, false, [2736], [11]⟩,
        ⟨10794, true, false, [2736], [11]⟩,
        ⟨11026, true, false, [2736, 2692], [5, 11]⟩,
        ⟨11026, true, false, [2736, 2692], [5, 11]⟩,
        ⟨11025, true, false, [2736, 2692], [5, 11]⟩,
        ⟨1028, false, false, [2736, 2692, 79165], []⟩,
        ⟨50, false, false, [2736, 2692, 79165], []⟩,
        ⟨11027, false, false, [2736, 2692], []⟩,
        ⟨10817, false, false, [2736, 2692], []⟩,
        ⟨10793, false, false, [2736, 2692], []⟩,
        ⟨10793, false, false, [2736, 2692], []⟩,
        ⟨11029, true, false, [2736], [79163]⟩,
        ⟨11029, true, false, [2736], [79163]⟩,
        ⟨11028, true, false, [2736], [79163]⟩,
        ⟨11046, false, false, [2736, 2729], []⟩,
        ⟨11047, true, false, [2736], [77877]⟩,
        ⟨11041, true, false, [], [2739, 77877]⟩,
        ⟨11048, true, false, [], [77877]⟩
      ]⟩,
    ⟨[2741, 77877], [2741, 77877], .contexts []⟩,
    ⟨[2743], [2740], .source 1436⟩,
    ⟨[2740], [2740], .contexts []⟩,
    ⟨[2745], [2681, 2615], .source 1437⟩,
    ⟨[78237, 5], [78237, 5], .contexts []⟩,
    ⟨[2747], [2744], .source 1438⟩,
    ⟨[2744], [2744], .contexts []⟩,
    ⟨[78237, 5], [2747, 77621], .contexts [
        ⟨11054, false, false, [], []⟩,
        ⟨11053, false, false, [2744], [78237, 5]⟩,
        ⟨10906, true, false, [2744, 2681], [5]⟩,
        ⟨11031, true, false, [2744], [13, 5]⟩,
        ⟨1578, false, false, [2744, 77619], []⟩,
        ⟨108, false, false, [2744, 77619], []⟩,
        ⟨3749, false, false, [2744], []⟩,
        ⟨3967, false, false, [2744], []⟩,
        ⟨3753, false, false, [2744], []⟩,
        ⟨3753, false, false, [2744], []⟩,
        ⟨11056, true, false, [], [77621]⟩,
        ⟨11056, true, false, [], [77621]⟩,
        ⟨11055, true, false, [], [77621]⟩
      ]⟩,
    ⟨[2745], [2746], .contexts [
        ⟨11055, true, true, [], []⟩
      ]⟩,
    ⟨[2687, 79169], [2687, 79169], .contexts []⟩,
    ⟨[2749], [2687, 2697], .source 1439⟩,
    ⟨[2749, 78113], [2749, 78113], .contexts []⟩,
    ⟨[2749, 78113], [2749, 78113], .contexts []⟩,
    ⟨[79165], [79165], .contexts []⟩,
    ⟨[2751], [2748], .source 1440⟩,
    ⟨[2748], [2748], .contexts []⟩,
    ⟨[78113, 15], [2751, 79165], .contexts [
        ⟨11062, true, false, [2748], [15]⟩,
        ⟨11061, true, false, [2748], [15]⟩,
        ⟨6074, true, false, [], [15]⟩,
        ⟨11060, false, false, [2748], [78115, 9, 15]⟩,
        ⟨10983, true, false, [2748, 2687], [9, 15]⟩,
        ⟨11059, true, false, [2748], [15, 9, 15]⟩,
        ⟨11059, true, false, [2748], [15, 9, 15]⟩,
        ⟨10968, true, false, [2748], [15, 9, 15]⟩,
        ⟨10965, true, false, [2748], [15, 9, 15]⟩,
        ⟨835, false, false, [2748, 79165], []⟩,
        ⟨11063, false, false, [2748], []⟩,
        ⟨11015, false, false, [2748], []⟩,
        ⟨11065, true, false, [], [79165]⟩,
        ⟨11065, true, false, [], [79165]⟩,
        ⟨11064, true, false, [], [79165]⟩
      ]⟩,
    ⟨[79165, 15], [2749, 78113], .contexts [
        ⟨11066, true, false, [2750], [15]⟩,
        ⟨3, false, false, [2750, 78113], []⟩,
        ⟨11064, false, true, [], [78113]⟩
      ]⟩,
    ⟨[79165, 5], [2737, 77877], .contexts [
        ⟨11027, false, false, [], []⟩,
        ⟨11046, false, false, [], []⟩,
        ⟨11045, false, false, [], []⟩,
        ⟨11045, false, false, [], []⟩
      ]⟩,
    ⟨[2721, 79165], [2721, 79165], .contexts []⟩,
    ⟨[2753], [2721, 2737], .source 1441⟩,
    ⟨[79165, 3, 5, 3], [2753, 2735, 79161], .contexts [
        ⟨11014, false, false, [], [5, 3]⟩,
        ⟨11014, false, false, [], [5, 3]⟩,
        ⟨11013, false, false, [2716], [5, 3]⟩,
        ⟨77, false, false, [2716, 79169], [5, 3]⟩,
        ⟨10969, false, false, [2716], [5, 3]⟩,
        ⟨11012, false, false, [2716], [5, 3]⟩,
        ⟨10963, false, false, [2716], [5, 3]⟩,
        ⟨10963, false, false, [2716], [5, 3]⟩,
        ⟨11015, false, false, [2716, 2685], [5, 3]⟩,
        ⟨11016, true, false, [], [2685, 79165, 5, 3]⟩,
        ⟨11017, true, false, [], [79165, 5, 3]⟩,
        ⟨11069, false, false, [], [5, 3]⟩,
        ⟨11069, false, false, [], [5, 3]⟩,
        ⟨10794, false, false, [2721], [3]⟩,
        ⟨11046, false, false, [2721], [3]⟩,
        ⟨11070, true, false, [], [77877, 3]⟩,
        ⟨11044, false, false, [2753], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 173. -/
def y322TCContextRaw173 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2755], [2753, 2735], .source 1442⟩,
    ⟨[79161, 5], [79161, 5], .contexts []⟩,
    ⟨[79161], [79161], .contexts []⟩,
    ⟨[2757], [2737, 2743], .source 1443⟩,
    ⟨[77881, 5], [77881, 5], .contexts []⟩,
    ⟨[2759], [2756], .source 1444⟩,
    ⟨[2761], [2759, 2689], .source 1445⟩,
    ⟨[77881, 5], [2761, 78235], .contexts [
        ⟨11076, false, false, [], []⟩,
        ⟨11075, false, false, [2756], [77881, 5]⟩,
        ⟨11051, false, false, [2756, 2737], [77881, 5]⟩,
        ⟨11052, false, false, [2756, 2737], [77881, 5]⟩,
        ⟨11052, false, false, [2756, 2737], [77881, 5]⟩,
        ⟨5235, true, false, [2756, 2737, 2740], [5]⟩,
        ⟨4995, true, false, [2756, 2737, 2740], [5]⟩,
        ⟨11049, false, false, [2756, 2737, 2740], [13, 5]⟩,
        ⟨11068, true, false, [2756], [13, 5]⟩,
        ⟨1578, false, false, [2756, 79165], []⟩,
        ⟨108, false, false, [2756, 79165], []⟩,
        ⟨11019, false, false, [2756], []⟩,
        ⟨6724, false, false, [2756, 2689], []⟩,
        ⟨11077, true, false, [], [2689, 78235]⟩,
        ⟨11078, true, false, [], [78235]⟩
      ]⟩,
    ⟨[2763], [2760], .source 1446⟩,
    ⟨[78235, 5], [2763, 77881], .contexts [
        ⟨11079, true, false, [2760], [5]⟩,
        ⟨49, false, false, [2760, 77881], []⟩,
        ⟨11080, true, false, [], [77881]⟩
      ]⟩,
    ⟨[2765], [2685, 2749], .source 1447⟩,
    ⟨[2765, 78111], [2765, 78111], .contexts []⟩,
    ⟨[2767], [2764], .source 1448⟩,
    ⟨[2764], [2764], .contexts []⟩,
    ⟨[78111, 15], [2767, 79165], .contexts [
        ⟨11083, true, false, [2764], [15]⟩,
        ⟨6070, true, false, [], [15]⟩,
        ⟨11082, false, false, [2764], [78113, 1, 15]⟩,
        ⟨11067, true, false, [2764, 2685], [1, 15]⟩,
        ⟨11020, true, false, [2764], [15, 1, 15]⟩,
        ⟨3731, false, false, [2764, 79165], []⟩,
        ⟨11063, false, false, [2764], []⟩,
        ⟨11015, false, false, [2764], []⟩,
        ⟨11085, true, false, [], [79165]⟩,
        ⟨11085, true, false, [], [79165]⟩,
        ⟨11084, true, false, [], [79165]⟩
      ]⟩,
    ⟨[2769], [2751, 2765], .source 1449⟩,
    ⟨[78113], [2769, 78111], .contexts [
        ⟨11062, true, false, [2748], []⟩,
        ⟨11062, true, false, [2748], []⟩,
        ⟨11061, true, false, [2748], []⟩,
        ⟨11067, true, false, [2748], []⟩,
        ⟨11086, true, false, [2748, 2766], [15]⟩,
        ⟨3, false, false, [2748, 2766, 78111], []⟩,
        ⟨11084, false, true, [2748], [78111]⟩,
        ⟨11083, false, false, [2748], []⟩,
        ⟨11064, true, false, [], [2765, 78111]⟩,
        ⟨11087, true, false, [], [78111]⟩
      ]⟩,
    ⟨[2771], [2768], .source 1450⟩,
    ⟨[2768], [2768], .contexts []⟩,
    ⟨[78113], [2769, 78111], .contexts [
        ⟨11088, false, false, [], []⟩
      ]⟩,
    ⟨[2777], [2771, 1379], .source 1453⟩,
    ⟨[2779], [2777, 2769], .source 1454⟩,
    ⟨[2657, 78233], [2657, 78233], .contexts []⟩,
    ⟨[2657, 78233], [2657, 78233], .contexts []⟩,
    ⟨[78233, 9], [78233, 9], .contexts []⟩,
    ⟨[2659], [2659], .contexts []⟩,
    ⟨[2656], [2656], .contexts []⟩,
    ⟨[78233, 9], [2659, 77439], .contexts [
        ⟨11096, false, false, [], []⟩,
        ⟨11095, true, false, [2656], [9]⟩,
        ⟨11094, true, false, [2656], [9]⟩,
        ⟨6496, true, false, [], [9]⟩,
        ⟨10997, true, false, [2656], [1, 9]⟩,
        ⟨10996, true, false, [2656], [1, 9]⟩,
        ⟨10995, true, false, [2656], [1, 9]⟩,
        ⟨10994, true, false, [2656], [1, 9]⟩,
        ⟨10985, true, false, [2656], [9, 1, 9]⟩,
        ⟨10985, true, false, [2656], [9, 1, 9]⟩,
        ⟨10984, true, false, [2656], [9, 1, 9]⟩,
        ⟨10988, true, false, [2656], [9, 1, 9]⟩,
        ⟨10987, true, false, [2656], [9, 1, 9]⟩,
        ⟨1022, false, false, [2656, 77443], []⟩,
        ⟨787, false, false, [2656, 77443], []⟩,
        ⟨3510, false, false, [2656], [1]⟩,
        ⟨2330, false, false, [2656], []⟩,
        ⟨2331, false, false, [2656], []⟩,
        ⟨2231, false, false, [2656], []⟩,
        ⟨2231, false, false, [2656], []⟩,
        ⟨3523, false, false, [2656], []⟩,
        ⟨11098, true, false, [], [77439]⟩,
        ⟨11098, true, false, [], [77439]⟩,
        ⟨10920, true, false, [], [77439]⟩,
        ⟨11097, true, false, [], [77439]⟩
      ]⟩,
    ⟨[77439, 9], [2657, 78233], .contexts [
        ⟨11099, true, false, [2658], [9]⟩,
        ⟨76, false, false, [2658, 78233], []⟩,
        ⟨10922, true, false, [], [78233]⟩
      ]⟩,
    ⟨[78235, 11], [2709, 78235], .contexts [
        ⟨10998, false, false, [], []⟩,
        ⟨6500, true, false, [], [11]⟩,
        ⟨10993, false, false, [2704], [78237, 9, 11]⟩,
        ⟨10926, true, false, [2704, 1033], [9, 11]⟩,
        ⟨10992, true, false, [2704], [11, 9, 11]⟩,
        ⟨10992, true, false, [2704], [11, 9, 11]⟩,
        ⟨10991, true, false, [2704], [11, 9, 11]⟩,
        ⟨10990, true, false, [2704], [11, 9, 11]⟩,
        ⟨4749, true, false, [2704], [11, 9, 11]⟩,
        ⟨966, false, false, [2704, 77447], []⟩,
        ⟨967, false, false, [2704, 77447], []⟩,
        ⟨10986, false, false, [2704], [9]⟩,
        ⟨10994, false, false, [2704], []⟩,
        ⟨10995, false, false, [2704], []⟩,
        ⟨10996, false, false, [2704], []⟩,
        ⟨10997, false, false, [2704], []⟩,
        ⟨6724, false, false, [2704, 2657], []⟩,
        ⟨10999, true, false, [], [2657, 78235]⟩,
        ⟨11000, true, false, [], [78235]⟩
      ]⟩,
    ⟨[2709, 78235], [2709, 78235], .contexts []⟩,
    ⟨[78233, 11], [78233, 11], .contexts []⟩,
    ⟨[2783], [2708], .source 1456⟩,
    ⟨[2708], [2708], .contexts []⟩,
    ⟨[78233, 11], [2783, 78233], .contexts [
        ⟨11103, false, false, [], []⟩,
        ⟨6496, true, false, [], [11]⟩,
        ⟨11102, true, false, [2708], [1, 11]⟩,
        ⟨11102, true, false, [2708], [1, 11]⟩,
        ⟨11101, true, false, [2708], [1, 11]⟩,
        ⟨10998, true, false, [2708], [1, 11]⟩,
        ⟨1000, false, false, [2708, 78235], []⟩,
        ⟨6728, false, false, [2708], []⟩,
        ⟨6727, false, false, [2708], []⟩,
        ⟨6730, false, false, [2708], []⟩,
        ⟨11105, true, false, [], [78233]⟩,
        ⟨11105, true, false, [], [78233]⟩,
        ⟨11104, true, false, [], [78233]⟩
      ]⟩,
    ⟨[2763, 77881], [2763, 77881], .contexts []⟩,
    ⟨[77881], [77881], .contexts []⟩,
    ⟨[77443, 3], [2665, 77575], .contexts [
        ⟨11004, false, false, [], []⟩,
        ⟨11005, false, false, [], []⟩,
        ⟨11002, false, false, [], []⟩,
        ⟨11003, false, false, [], []⟩,
        ⟨11003, false, false, [], []⟩
      ]⟩,
    ⟨[2664], [2664], .contexts []⟩,
    ⟨[77573, 3], [2711, 77441], .contexts [
        ⟨3102, true, false, [], [3]⟩,
        ⟨11109, true, false, [2664], [9, 3]⟩,
        ⟨1010, false, false, [2664, 77443], []⟩,
        ⟨3511, false, false, [2664], []⟩,
        ⟨3510, false, false, [2664], []⟩,
        ⟨3513, false, false, [2664], []⟩,
        ⟨11110, true, false, [], [77441]⟩,
        ⟨11110, true, false, [], [77441]⟩,
        ⟨11006, true, false, [], [77441]⟩
      ]⟩,
    ⟨[2727, 78233], [2727, 78233], .contexts []⟩,
    ⟨[78233, 13, 5], [2727, 78231], .contexts [
        ⟨11022, false, false, [], [5]⟩,
        ⟨11022, false, false, [], [5]⟩,
        ⟨6496, true, false, [], [13, 5]⟩,
        ⟨11019, true, false, [2688], [1, 13, 5]⟩,
        ⟨3338, false, false, [2688, 79165], [5]⟩,
        ⟨389, false, false, [2688, 79165], [5]⟩,
        ⟨11020, false, false, [2688], [13, 1, 5]⟩,
        ⟨10972, false, false, [2688, 2685], [1, 5]⟩,
        ⟨11021, true, false, [2688], [78235, 1, 5]⟩,
        ⟨6496, false, false, [2688, 2723], [5]⟩,
        ⟨6730, false, false, [2688, 2723], [5]⟩,
        ⟨11023, true, false, [], [2723, 78233, 5]⟩,
        ⟨11024, true, false, [], [78233, 5]⟩,
        ⟨11112, false, false, [], [5]⟩,
        ⟨11112, false, false, [], [5]⟩,
        ⟨6492, false, false, [2727], []⟩
      ]⟩,
    ⟨[2791], [2726], .source 1460⟩,
    ⟨[2726], [2726], .contexts []⟩,
    ⟨[2659, 77439], [2659, 77439], .contexts []⟩,
    ⟨[2799], [2741, 2735], .source 1464⟩,
    ⟨[2735, 79161], [2735, 79161], .contexts []⟩,
    ⟨[2801], [2798], .source 1465⟩,
    ⟨[2735, 79165], [2735, 79165], .contexts []⟩,
    ⟨[2815], [2749, 2769], .source 1472⟩,
    ⟨[2817], [2735, 2815], .source 1473⟩,
    ⟨[2817, 78109], [2817, 78109], .contexts []⟩,
    ⟨[2817, 78109], [2817, 78109], .contexts []⟩,
    ⟨[2817, 78109, 15], [77877], .contexts [
        ⟨11124, true, false, [], [15]⟩,
        ⟨11123, true, false, [], [15]⟩,
        ⟨6067, true, false, [2817], [15]⟩,
        ⟨11122, false, false, [], [78111, 5, 15]⟩,
        ⟨11121, false, false, [2735], [78111, 5, 15]⟩,
        ⟨11091, true, false, [2735, 2749], [5, 15]⟩,
        ⟨11067, true, false, [2735], [5, 15]⟩,
        ⟨11120, true, false, [], [15, 5, 15]⟩,
        ⟨11120, true, false, [], [15, 5, 15]⟩,
        ⟨11043, false, false, [], [79165, 15, 5, 15]⟩,
        ⟨10815, true, false, [2736], [15, 5, 15]⟩,
        ⟨10792, true, false, [2736], [15, 5, 15]⟩,
        ⟨11040, false, false, [2736], [5, 15, 5, 15]⟩,
        ⟨1504, false, false, [77877], []⟩
      ]⟩,
    ⟨[2819], [2816], .source 1474⟩,
    ⟨[2816], [2816], .contexts []⟩,
    ⟨[77877, 15], [2817, 78109], .contexts [
        ⟨11126, false, false, [2818], [77877, 15]⟩,
        ⟨11127, false, false, [2818], [77877, 15]⟩,
        ⟨11127, false, false, [2818], [77877, 15]⟩,
        ⟨4986, true, false, [2818, 2816], [15]⟩,
        ⟨11125, true, false, [2818, 2816], [15]⟩,
        ⟨3, false, false, [2818, 78109], []⟩,
        ⟨11126, false, true, [], [78109]⟩
      ]⟩,
    ⟨[2821], [1059, 2817], .source 1475⟩,
    ⟨[77877, 15], [2817, 78109], .contexts [
        ⟨11128, false, false, [], []⟩,
        ⟨11123, false, false, [], []⟩,
        ⟨11124, false, false, [], []⟩,
        ⟨11124, false, false, [], []⟩
      ]⟩,
    ⟨[78109, 1], [78109, 1], .contexts []⟩,
    ⟨[2823], [2820], .source 1476⟩,
    ⟨[2825], [2823, 2817], .source 1477⟩,
    ⟨[79161, 15], [79161, 15], .contexts []⟩,
    ⟨[2827], [2737, 2817], .source 1478⟩]

/-- Exact literal claimed equations and contextual derivations, block 174. -/
def y322TCContextRaw174 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79161, 15], [2827, 78107], .contexts [
        ⟨11134, false, false, [], []⟩,
        ⟨11118, true, false, [2734], [15]⟩,
        ⟨11118, true, false, [2734], [15]⟩,
        ⟨11044, true, false, [2734], [15]⟩,
        ⟨245, false, false, [2734, 77877], []⟩,
        ⟨246, false, false, [2734, 77877], []⟩,
        ⟨11130, false, false, [2734], [3]⟩,
        ⟨6063, false, false, [2734, 2817], []⟩,
        ⟨6190, false, false, [2734, 2817], []⟩,
        ⟨11039, true, false, [], [2817, 78107]⟩,
        ⟨11135, true, false, [], [78107]⟩
      ]⟩,
    ⟨[2829], [2826], .source 1479⟩,
    ⟨[2747, 77621], [2747, 77621], .contexts []⟩,
    ⟨[78237, 5], [2747, 77621], .contexts [
        ⟨11054, false, false, [], []⟩,
        ⟨11057, false, false, [], []⟩,
        ⟨11138, false, false, [], []⟩,
        ⟨11138, false, false, [], []⟩
      ]⟩,
    ⟨[78239], [2659, 77447], .contexts [
        ⟨10928, false, false, [], []⟩
      ]⟩,
    ⟨[2831], [2659, 2661], .source 1480⟩,
    ⟨[77621, 11], [77621, 11], .contexts []⟩,
    ⟨[2745], [2746], .contexts [
        ⟨11058, false, false, [], []⟩
      ]⟩,
    ⟨[2833], [2745, 2831], .source 1481⟩,
    ⟨[77621, 11], [2833, 78849], .contexts [
        ⟨11142, false, false, [], []⟩,
        ⟨11139, true, false, [2746], [11]⟩,
        ⟨275, false, false, [2746, 78237], []⟩,
        ⟨276, false, false, [2746, 78237], []⟩,
        ⟨6502, false, false, [2746], [5]⟩,
        ⟨11140, false, false, [2746], [5]⟩,
        ⟨10927, false, false, [2746], [5]⟩,
        ⟨10927, false, false, [2746], [5]⟩,
        ⟨10931, false, false, [2746, 2659], []⟩,
        ⟨11141, true, false, [2746], [78849]⟩,
        ⟨9887, false, false, [2746, 2831], []⟩,
        ⟨11143, true, false, [], [2831, 78849]⟩,
        ⟨11144, true, false, [], [78849]⟩
      ]⟩,
    ⟨[2835], [2832], .source 1482⟩,
    ⟨[2837], [2745, 1459], .source 1483⟩,
    ⟨[2839], [2836], .source 1484⟩,
    ⟨[2841], [2745, 2839], .source 1485⟩,
    ⟨[2843], [2840], .source 1486⟩,
    ⟨[77623], [2843, 77621], .contexts [
        ⟨11149, false, false, [2840], [77623]⟩,
        ⟨11058, false, false, [2840], [2839, 77623]⟩,
        ⟨11148, false, false, [2840, 2746], [77623]⟩,
        ⟨49, true, false, [2840, 2746, 2836, 77623], []⟩,
        ⟨3752, true, false, [2840, 2746, 2836], [5, 5]⟩,
        ⟨11139, true, false, [2840, 2746, 2836, 2746], [15, 5, 5]⟩,
        ⟨2006, false, false, [2840, 2746, 2836, 2746, 78237], [5]⟩,
        ⟨20, false, false, [2840, 2746, 2836, 2746, 78237], [5]⟩,
        ⟨6720, false, false, [2840, 2746, 2836, 2746], [5]⟩,
        ⟨6713, false, false, [2840, 2746, 2836, 2746, 1459], [5]⟩,
        ⟨11143, true, false, [2840, 2746, 2836], [1459, 78237, 5]⟩,
        ⟨11147, true, false, [2840, 2746, 2836], [78237, 5]⟩,
        ⟨11139, false, false, [2840, 2746], []⟩,
        ⟨11150, true, false, [], [77621]⟩
      ]⟩,
    ⟨[2842], [2842], .contexts []⟩,
    ⟨[77621, 1], [2841, 77625], .contexts [
        ⟨11151, true, false, [2842], [1]⟩,
        ⟨3755, false, false, [2842], []⟩,
        ⟨3965, false, false, [2842], []⟩,
        ⟨11152, true, false, [], [77625]⟩,
        ⟨11152, true, false, [], [77625]⟩,
        ⟨11150, false, true, [], [77625]⟩
      ]⟩,
    ⟨[2745, 78237], [2745, 78237], .contexts []⟩,
    ⟨[2845], [2745, 2659], .source 1487⟩,
    ⟨[2841, 77625], [2841, 77625], .contexts []⟩,
    ⟨[2841, 77625], [2841, 77625], .contexts []⟩,
    ⟨[77621, 1], [2841, 77625], .contexts [
        ⟨11153, false, false, [], []⟩,
        ⟨11156, false, false, [], []⟩,
        ⟨11157, false, false, [], []⟩,
        ⟨11157, false, false, [], []⟩
      ]⟩,
    ⟨[77621, 0], [77621, 1], .contexts [
        ⟨19, false, false, [77621], []⟩
      ]⟩,
    ⟨[77443, 5], [77443, 5], .contexts []⟩,
    ⟨[77625], [77625], .contexts []⟩,
    ⟨[2847], [2844], .source 1488⟩,
    ⟨[2849], [2847, 2841], .source 1489⟩,
    ⟨[77443, 5], [2849, 77625], .contexts [
        ⟨11160, false, false, [], []⟩,
        ⟨11155, false, false, [2844], [77443, 5]⟩,
        ⟨10989, true, false, [2844, 2745], [5]⟩,
        ⟨11154, true, false, [2844], [1, 5]⟩,
        ⟨11154, true, false, [2844], [1, 5]⟩,
        ⟨11058, false, false, [2844], [78237, 1, 5]⟩,
        ⟨49, true, false, [2844, 2746, 78237], [1, 5]⟩,
        ⟨11057, false, false, [2844, 2746], [5, 1, 5]⟩,
        ⟨1509, false, false, [2844, 77621], []⟩,
        ⟨11159, false, false, [2844], []⟩,
        ⟨11158, false, false, [2844], []⟩,
        ⟨11161, false, false, [2844, 2841], []⟩,
        ⟨11162, true, false, [], [2841, 77625]⟩,
        ⟨11163, true, false, [], [77625]⟩
      ]⟩,
    ⟨[2851], [2848], .source 1490⟩,
    ⟨[2755, 79161], [2755, 79161], .contexts []⟩,
    ⟨[79161, 5, 1], [2755, 79159], .contexts [
        ⟨11073, false, false, [], [1]⟩,
        ⟨11073, false, false, [], [1]⟩,
        ⟨11039, true, false, [], [2735, 79161, 5, 1]⟩,
        ⟨11044, true, false, [2737], [5, 1]⟩,
        ⟨11068, true, false, [], [3, 5, 1]⟩,
        ⟨2455, false, false, [79165], [1]⟩,
        ⟨266, false, false, [79165], [1]⟩,
        ⟨11071, false, false, [], [1]⟩,
        ⟨11072, true, false, [], [79161, 1]⟩,
        ⟨11074, false, false, [2755], [1]⟩,
        ⟨24, true, false, [], [2755, 79161, 1]⟩,
        ⟨11166, false, false, [], [1]⟩,
        ⟨11166, false, false, [], [1]⟩,
        ⟨10787, false, false, [2755], []⟩
      ]⟩,
    ⟨[79161, 1], [79159], .contexts [
        ⟨10819, false, false, [], []⟩
      ]⟩,
    ⟨[79161, 1], [79159], .contexts [
        ⟨11168, false, false, [], []⟩,
        ⟨10820, false, false, [], []⟩,
        ⟨10786, false, false, [], []⟩,
        ⟨10786, false, false, [], []⟩
      ]⟩,
    ⟨[2853], [2754], .source 1491⟩,
    ⟨[2754], [2754], .contexts []⟩,
    ⟨[2827, 78107], [2827, 78107], .contexts []⟩,
    ⟨[2761, 78235], [2761, 78235], .contexts []⟩,
    ⟨[77881, 5], [2761, 78235], .contexts [
        ⟨11076, false, false, [], []⟩,
        ⟨11079, false, false, [], []⟩,
        ⟨11173, false, false, [], []⟩,
        ⟨11173, false, false, [], []⟩
      ]⟩,
    ⟨[2760], [2760], .contexts []⟩,
    ⟨[77881, 1], [2761, 78231], .contexts [
        ⟨11080, false, false, [2762], [77881, 1]⟩,
        ⟨11175, false, false, [2762], [77881, 1]⟩,
        ⟨11175, false, false, [2762], [77881, 1]⟩,
        ⟨11108, true, false, [2762, 2760], [1]⟩,
        ⟨1485, true, false, [2762, 2760, 77881], [1]⟩,
        ⟨11174, false, false, [2762, 2760], [1, 5, 1, 1]⟩,
        ⟨6496, false, false, [2762], [5, 1, 1]⟩,
        ⟨6492, false, false, [2762], [1, 1]⟩,
        ⟨18, false, false, [2762, 78231], []⟩,
        ⟨11080, false, true, [], [78231]⟩
      ]⟩,
    ⟨[2861], [2761, 1465], .source 1495⟩,
    ⟨[2863], [2861, 2763], .source 1496⟩,
    ⟨[2865], [2862], .source 1497⟩,
    ⟨[2865, 77881], [2865, 77881], .contexts []⟩,
    ⟨[77883], [2865, 77881], .contexts [
        ⟨4997, true, false, [], []⟩,
        ⟨11178, false, false, [2862], [77881, 15]⟩,
        ⟨11081, true, false, [2862, 2861], [15]⟩,
        ⟨11177, false, false, [2862], [78235, 5, 15]⟩,
        ⟨6725, true, false, [2862, 2761], [5, 15]⟩,
        ⟨11174, true, false, [2862], [15, 5, 15]⟩,
        ⟨289, false, false, [2862, 77881], []⟩,
        ⟨11108, true, false, [2862], []⟩,
        ⟨11179, true, false, [], [77881]⟩,
        ⟨11180, false, false, [], []⟩
      ]⟩,
    ⟨[2867], [2865, 2761], .source 1498⟩,
    ⟨[2869], [2866], .source 1499⟩,
    ⟨[78231], [2869, 77885], .contexts [
        ⟨11182, false, false, [2866], [78231]⟩,
        ⟨11176, true, false, [2866, 2865], []⟩,
        ⟨11181, true, false, [2866], [1]⟩,
        ⟨5000, false, false, [2866], []⟩,
        ⟨5234, false, false, [2866], []⟩,
        ⟨24, true, false, [2866], [77885]⟩,
        ⟨11183, true, false, [], [77885]⟩
      ]⟩,
    ⟨[2867], [2868], .contexts [
        ⟨11183, true, true, [], []⟩
      ]⟩,
    ⟨[2867], [2868], .contexts [
        ⟨11185, false, false, [], []⟩
      ]⟩,
    ⟨[2869, 77885], [2869, 77885], .contexts []⟩,
    ⟨[78231], [2869, 77885], .contexts [
        ⟨11184, false, false, [], []⟩,
        ⟨11187, false, false, [], []⟩
      ]⟩,
    ⟨[2875], [2867, 2791], .source 1502⟩,
    ⟨[2877], [2875, 2869], .source 1503⟩,
    ⟨[77887, 1], [2868, 1459, 78225], .contexts [
        ⟨11183, false, false, [2868], [77887, 1]⟩,
        ⟨5003, true, false, [2868, 2866], [1]⟩,
        ⟨11188, true, false, [2868, 2866, 2868], [3, 1]⟩,
        ⟨6489, false, false, [2868, 2866, 2868], [1]⟩,
        ⟨6558, false, false, [2868, 2866, 2868], [1]⟩,
        ⟨24, true, false, [2868, 2866, 2868], [78229, 1]⟩,
        ⟨11186, true, false, [2868, 2866], [78229, 1]⟩,
        ⟨6486, false, false, [2868], []⟩,
        ⟨6485, true, false, [2868], []⟩,
        ⟨6485, true, false, [2868], []⟩,
        ⟨6560, true, false, [2868], []⟩,
        ⟨6559, true, false, [2868], []⟩,
        ⟨6701, false, false, [2868, 1464], [78229, 1]⟩,
        ⟨6741, true, false, [2868, 1464, 1458], [1]⟩,
        ⟨911, true, false, [2868, 1464, 1458, 78229], [1]⟩,
        ⟨6744, false, false, [2868, 1464, 1458], [1, 1]⟩,
        ⟨6745, false, false, [2868, 1464, 1458], [1, 1]⟩,
        ⟨18, false, false, [2868, 1464, 78225], []⟩,
        ⟨6714, true, false, [2868], [78225]⟩,
        ⟨6743, false, false, [2868], []⟩,
        ⟨6715, true, false, [2868], [78225]⟩,
        ⟨6745, false, false, [2868], []⟩
      ]⟩,
    ⟨[2879], [2867, 1459], .source 1504⟩,
    ⟨[77887, 1], [2879, 78225], .contexts [
        ⟨11191, false, false, [], []⟩,
        ⟨11186, true, false, [], [1459, 78225]⟩,
        ⟨11192, true, false, [], [78225]⟩
      ]⟩,
    ⟨[78111, 13], [2779, 78111], .contexts [
        ⟨11088, true, false, [2768], [13]⟩,
        ⟨6074, true, false, [2768], [13]⟩,
        ⟨6174, true, false, [2768, 1380], [9, 13]⟩,
        ⟨6174, true, false, [2768, 1380], [9, 13]⟩,
        ⟨6168, true, false, [2768, 1380], [9, 13]⟩,
        ⟨6165, true, false, [2768, 1380], [9, 13]⟩,
        ⟨1650, false, false, [2768, 1380, 78115], []⟩,
        ⟨77, false, false, [2768, 1380, 78115], []⟩,
        ⟨6152, false, false, [2768, 1380], []⟩,
        ⟨6159, false, false, [2768, 1380], []⟩,
        ⟨6175, true, false, [2768], [78113]⟩,
        ⟨6175, true, false, [2768], [78113]⟩,
        ⟨6166, false, true, [2768], [78113]⟩,
        ⟨11091, false, false, [2768, 1379], []⟩,
        ⟨11089, true, false, [], [1379, 2769, 78111]⟩,
        ⟨11092, true, false, [], [2769, 78111]⟩,
        ⟨11093, true, false, [], [78111]⟩
      ]⟩,
    ⟨[2779, 78111], [2779, 78111], .contexts []⟩,
    ⟨[2779, 78109], [2779, 78109], .contexts []⟩,
    ⟨[2779, 78109], [2779, 78109], .contexts []⟩,
    ⟨[78109, 13], [78109, 13], .contexts []⟩,
    ⟨[78231], [2869, 77885], .contexts [
        ⟨11188, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 175. -/
def y322TCContextRaw175 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78233, 5], [2869, 77885], .contexts [
        ⟨6733, false, false, [], []⟩,
        ⟨11199, false, false, [], []⟩,
        ⟨11187, false, false, [], []⟩,
        ⟨11187, false, false, [], []⟩
      ]⟩,
    ⟨[77885], [77885], .contexts []⟩,
    ⟨[2883], [2657, 2869], .source 1506⟩,
    ⟨[2885], [2882], .source 1507⟩,
    ⟨[77885, 9], [2885, 77437], .contexts [
        ⟨11202, false, false, [2882], [77885, 9]⟩,
        ⟨10923, false, false, [2882], [2869, 77885, 9]⟩,
        ⟨11201, true, false, [2882, 2658, 2869], [9]⟩,
        ⟨11200, true, false, [2882, 2658], [9]⟩,
        ⟨6735, true, false, [2882, 2658], [9]⟩,
        ⟨1034, true, false, [2882, 2658, 78233], [9]⟩,
        ⟨11096, false, false, [2882, 2658], [5, 9, 9]⟩,
        ⟨11099, false, false, [2882, 2658], [5, 9, 9]⟩,
        ⟨11116, false, false, [2882, 2658], [5, 9, 9]⟩,
        ⟨11116, false, false, [2882, 2658], [5, 9, 9]⟩,
        ⟨2228, false, false, [2882], [9, 9]⟩,
        ⟨76, false, false, [2882, 77437], []⟩,
        ⟨11203, true, false, [], [77437]⟩
      ]⟩,
    ⟨[2783, 78233], [2783, 78233], .contexts []⟩,
    ⟨[2887], [2783, 2869], .source 1508⟩,
    ⟨[77885, 11], [77885, 11], .contexts []⟩,
    ⟨[2889], [2886], .source 1509⟩,
    ⟨[2891], [2889, 2869], .source 1510⟩,
    ⟨[2877, 77885], [2877, 77885], .contexts []⟩,
    ⟨[77885, 13, 3], [2877, 77887], .contexts [
        ⟨11184, true, false, [2868], [13, 3]⟩,
        ⟨11113, true, false, [2868, 2726], [13, 3]⟩,
        ⟨1886, false, false, [2868, 2726, 78233], [3]⟩,
        ⟨6735, false, false, [2868, 2726], [3]⟩,
        ⟨6734, false, false, [2868, 2726], [3]⟩,
        ⟨6737, false, false, [2868, 2726], [3]⟩,
        ⟨11115, true, false, [2868], [78231, 3]⟩,
        ⟨11115, true, false, [2868], [78231, 3]⟩,
        ⟨11114, true, false, [2868], [78231, 3]⟩,
        ⟨11188, false, false, [2868, 2791], [3]⟩,
        ⟨11185, true, false, [], [2791, 2869, 77885, 3]⟩,
        ⟨11189, true, false, [], [2869, 77885, 3]⟩,
        ⟨11190, true, false, [], [77885, 3]⟩,
        ⟨11210, false, false, [], [3]⟩,
        ⟨11210, false, false, [], [3]⟩,
        ⟨5003, false, false, [2877], []⟩
      ]⟩,
    ⟨[77885, 3], [77887], .contexts [
        ⟨5003, false, false, [], []⟩,
        ⟨5232, false, false, [], []⟩,
        ⟨5007, false, false, [], []⟩,
        ⟨5007, false, false, [], []⟩
      ]⟩,
    ⟨[77887, 13], [77887, 13], .contexts []⟩,
    ⟨[77887], [77887], .contexts []⟩,
    ⟨[2893], [2876], .source 1511⟩,
    ⟨[2876], [2876], .contexts []⟩,
    ⟨[2885, 77437], [2885, 77437], .contexts []⟩,
    ⟨[2825, 78109], [2825, 78109], .contexts []⟩,
    ⟨[78109, 1, 3], [2825, 78107], .contexts [
        ⟨11131, false, false, [], [3]⟩,
        ⟨11131, false, false, [], [3]⟩,
        ⟨11129, false, false, [2820], [78109, 1, 3]⟩,
        ⟨11128, true, false, [2820, 1059], [1, 3]⟩,
        ⟨4991, true, false, [2820], [15, 1, 3]⟩,
        ⟨5354, false, false, [2820, 77877], [3]⟩,
        ⟨20, false, false, [2820, 77877], [3]⟩,
        ⟨11130, false, false, [2820], [3]⟩,
        ⟨6180, false, false, [2820, 2817], [3]⟩,
        ⟨11132, true, false, [], [2817, 78109, 3]⟩,
        ⟨11133, true, false, [], [78109, 3]⟩,
        ⟨11218, false, false, [], [3]⟩,
        ⟨11218, false, false, [], [3]⟩,
        ⟨6063, false, false, [2825], []⟩
      ]⟩,
    ⟨[78105, 3], [78105, 3], .contexts []⟩,
    ⟨[2905], [2824], .source 1517⟩,
    ⟨[2824], [2824], .contexts []⟩,
    ⟨[78105, 3], [2905, 78105], .contexts [
        ⟨11220, false, false, [], []⟩,
        ⟨6059, true, false, [], [3]⟩,
        ⟨11219, true, false, [2824], [1, 3]⟩,
        ⟨852, false, false, [2824, 78109], []⟩,
        ⟨853, false, false, [2824, 78109], []⟩,
        ⟨6186, false, false, [2824], [1]⟩,
        ⟨6082, false, false, [2824], []⟩,
        ⟨6083, false, false, [2824], []⟩,
        ⟨6058, false, false, [2824], []⟩,
        ⟨6058, false, false, [2824], []⟩,
        ⟨6194, false, false, [2824], []⟩,
        ⟨11222, true, false, [], [78105]⟩,
        ⟨11222, true, false, [], [78105]⟩,
        ⟨11221, true, false, [], [78105]⟩
      ]⟩,
    ⟨[2827, 78105], [2827, 78105], .contexts []⟩,
    ⟨[2827, 78105], [2827, 78105], .contexts []⟩,
    ⟨[2827, 78105], [2827, 78105], .contexts []⟩,
    ⟨[2827, 78103], [2827, 78103], .contexts []⟩,
    ⟨[2827, 78103], [2827, 78103], .contexts []⟩,
    ⟨[2829], [2826], .contexts [
        ⟨11137, false, false, [], []⟩
      ]⟩,
    ⟨[2826], [2826], .contexts []⟩,
    ⟨[78103, 1], [2829, 79161], .contexts [
        ⟨11228, true, false, [2826], [1]⟩,
        ⟨11227, true, false, [2826], [1]⟩,
        ⟨6055, true, false, [], [1]⟩,
        ⟨11226, true, false, [2826], [15, 1]⟩,
        ⟨11225, true, false, [2826], [15, 1]⟩,
        ⟨11224, true, false, [2826], [15, 1]⟩,
        ⟨6059, true, false, [], [15, 1]⟩,
        ⟨11172, true, false, [2826], [1, 15, 1]⟩,
        ⟨11172, true, false, [2826], [1, 15, 1]⟩,
        ⟨11136, true, false, [2826], [1, 15, 1]⟩,
        ⟨11134, true, false, [2826], [1, 15, 1]⟩,
        ⟨911, false, false, [2826, 79161], []⟩,
        ⟨11074, false, false, [2826], []⟩,
        ⟨11230, true, false, [], [79161]⟩,
        ⟨11230, true, false, [], [79161]⟩,
        ⟨11229, true, false, [], [79161]⟩
      ]⟩,
    ⟨[2827], [2828], .contexts [
        ⟨11137, true, true, [], []⟩
      ]⟩,
    ⟨[79159], [2827, 78103], .contexts [
        ⟨11169, true, false, [], []⟩,
        ⟨11231, true, false, [2828], [1]⟩,
        ⟨18, false, false, [2828, 78103], []⟩,
        ⟨11232, true, false, [], [78103]⟩,
        ⟨11227, false, false, [], []⟩
      ]⟩,
    ⟨[79159], [2827, 78103], .contexts [
        ⟨11233, false, false, [], []⟩,
        ⟨11228, false, false, [], []⟩
      ]⟩,
    ⟨[2911], [2829, 2853], .source 1520⟩,
    ⟨[2913], [2911, 2827], .source 1521⟩,
    ⟨[78105, 13], [2829, 79155], .contexts [
        ⟨11232, false, false, [2826], [78105, 13]⟩,
        ⟨11226, true, false, [2826, 2828, 2826], [13]⟩,
        ⟨11225, true, false, [2826, 2828, 2826], [13]⟩,
        ⟨11224, true, false, [2826, 2828, 2826], [13]⟩,
        ⟨6053, true, false, [2826, 2828], [13]⟩,
        ⟨11234, true, false, [2826, 2828, 2826], [15, 13]⟩,
        ⟨10784, false, false, [2826, 2828, 2826], [13]⟩,
        ⟨10822, false, false, [2826, 2828, 2826], [13]⟩,
        ⟨24, true, false, [2826, 2828, 2826], [79157, 13]⟩,
        ⟨11229, true, false, [2826, 2828], [79157, 13]⟩,
        ⟨10781, false, false, [2826], []⟩,
        ⟨10823, false, false, [2826], []⟩,
        ⟨11230, true, false, [], [79155]⟩,
        ⟨11230, true, false, [], [79155]⟩,
        ⟨11229, true, false, [], [79155]⟩
      ]⟩,
    ⟨[2833, 78849], [2833, 78849], .contexts []⟩,
    ⟨[2915], [2835, 2841], .source 1522⟩,
    ⟨[78847, 11], [2915, 77625], .contexts [
        ⟨9875, true, false, [], [11]⟩,
        ⟨11238, true, false, [2832], [1, 11]⟩,
        ⟨11238, true, false, [2832], [1, 11]⟩,
        ⟨11145, true, false, [2832], [1, 11]⟩,
        ⟨11142, true, false, [2832], [1, 11]⟩,
        ⟨1000, false, false, [2832, 77621], []⟩,
        ⟨11159, false, false, [2832], []⟩,
        ⟨11158, false, false, [2832], []⟩,
        ⟨11161, false, false, [2832, 2841], []⟩,
        ⟨11146, true, false, [], [2841, 77625]⟩,
        ⟨11239, true, false, [], [77625]⟩
      ]⟩,
    ⟨[2917], [2914], .source 1523⟩,
    ⟨[2237, 77261], [2237, 77261], .contexts []⟩,
    ⟨[2237, 77263, 13], [2841, 77625], .contexts [
        ⟨1211, true, false, [2237], [13]⟩,
        ⟨11242, true, false, [], [1, 13]⟩,
        ⟨11242, true, false, [], [1, 13]⟩,
        ⟨9299, true, false, [], [1, 13]⟩,
        ⟨3744, true, false, [], [13, 1, 13]⟩,
        ⟨3744, true, false, [], [13, 1, 13]⟩,
        ⟨3743, true, false, [], [13, 1, 13]⟩,
        ⟨3970, true, false, [], [13, 1, 13]⟩,
        ⟨3750, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3750, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3969, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3968, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [77621], []⟩,
        ⟨11159, false, false, [], []⟩,
        ⟨11158, false, false, [], []⟩
      ]⟩,
    ⟨[77263, 13], [77263, 13], .contexts []⟩,
    ⟨[2919], [2236], .source 1524⟩,
    ⟨[2921], [2919, 2841], .source 1525⟩,
    ⟨[77263, 13], [2921, 77625], .contexts [
        ⟨11244, false, false, [], []⟩,
        ⟨11243, false, false, [2236], []⟩,
        ⟨11161, false, false, [2236, 2841], []⟩,
        ⟨11245, true, false, [], [2841, 77625]⟩,
        ⟨11246, true, false, [], [77625]⟩
      ]⟩,
    ⟨[2923], [2920], .source 1526⟩,
    ⟨[2843, 77621], [2843, 77621], .contexts []⟩,
    ⟨[77623], [2843, 77621], .contexts [
        ⟨11151, false, false, [], []⟩,
        ⟨11249, false, false, [], []⟩
      ]⟩,
    ⟨[77623], [2843, 77621], .contexts [
        ⟨11250, false, false, [], []⟩
      ]⟩,
    ⟨[77625, 15], [77625, 15], .contexts []⟩,
    ⟨[2849, 77625], [2849, 77625], .contexts []⟩,
    ⟨[2925], [2665, 2193], .source 1527⟩,
    ⟨[77629, 3], [77629, 3], .contexts []⟩,
    ⟨[2927], [2851, 2925], .source 1528⟩,
    ⟨[77629, 3], [2927, 78995], .contexts [
        ⟨11255, false, false, [], []⟩,
        ⟨3762, true, false, [], [3]⟩,
        ⟨3759, true, false, [], [5, 3]⟩,
        ⟨11253, true, false, [2848], [3, 5, 3]⟩,
        ⟨11253, true, false, [2848], [3, 5, 3]⟩,
        ⟨11164, true, false, [2848], [3, 5, 3]⟩,
        ⟨11160, true, false, [2848], [3, 5, 3]⟩,
        ⟨2018, false, false, [2848, 77443], []⟩,
        ⟨265, false, false, [2848, 77443], []⟩,
        ⟨11109, false, false, [2848], [5]⟩,
        ⟨10256, true, false, [2848, 2665, 2190], [5]⟩,
        ⟨49, false, false, [2848, 2665, 2190, 78995], []⟩,
        ⟨9137, true, false, [2848, 2665], [78995]⟩,
        ⟨11254, true, false, [2848], [78995]⟩,
        ⟨10254, false, false, [2848, 2925], []⟩,
        ⟨11165, true, false, [], [2925, 78995]⟩,
        ⟨11256, true, false, [], [78995]⟩
      ]⟩,
    ⟨[2929], [2926], .source 1529⟩,
    ⟨[1753, 79007], [1753, 79007], .contexts []⟩,
    ⟨[2931], [1755, 2929], .source 1530⟩,
    ⟨[79007], [2931, 77629], .contexts [
        ⟨11259, true, false, [1752], []⟩,
        ⟨11259, true, false, [1752], []⟩,
        ⟨10340, true, false, [1752], []⟩,
        ⟨11257, true, false, [1752, 2926], [3]⟩,
        ⟨35, false, false, [1752, 2926, 77629], []⟩,
        ⟨11258, true, false, [1752], [77629]⟩,
        ⟨7545, true, false, [], [2929, 77629]⟩,
        ⟨11260, true, false, [], [77629]⟩
      ]⟩,
    ⟨[2933], [2930], .source 1531⟩,
    ⟨[2930], [2930], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 176. -/
def y322TCContextRaw176 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77629, 13], [2933, 77267], .contexts [
        ⟨11261, true, false, [2930], [13]⟩,
        ⟨10332, false, false, [2930], []⟩,
        ⟨1410, false, false, [2930], []⟩,
        ⟨11263, true, false, [], [77267]⟩,
        ⟨11263, true, false, [], [77267]⟩,
        ⟨11262, true, false, [], [77267]⟩
      ]⟩,
    ⟨[2931, 77629], [2931, 77629], .contexts []⟩,
    ⟨[79007], [2931, 77629], .contexts [
        ⟨11261, false, false, [], []⟩,
        ⟨11265, false, false, [], []⟩
      ]⟩,
    ⟨[2935], [2933, 2569], .source 1532⟩,
    ⟨[2937], [2935, 2931], .source 1533⟩,
    ⟨[77629, 15], [2937, 77629], .contexts [
        ⟨11261, true, false, [2930], [15]⟩,
        ⟨10345, false, false, [2930], []⟩,
        ⟨11266, false, false, [2930, 2569], []⟩,
        ⟨11262, true, false, [], [2569, 2931, 77629]⟩,
        ⟨11267, true, false, [], [2931, 77629]⟩,
        ⟨11268, true, false, [], [77629]⟩
      ]⟩,
    ⟨[2913, 78103], [2913, 78103], .contexts []⟩,
    ⟨[78103, 5], [2913, 78103], .contexts [
        ⟨11233, true, false, [2826], [5]⟩,
        ⟨11167, true, false, [2826, 2754], [5]⟩,
        ⟨1509, false, false, [2826, 2754, 79161], []⟩,
        ⟨19, false, false, [2826, 2754, 79161], []⟩,
        ⟨11169, false, false, [2826, 2754], []⟩,
        ⟨11171, true, false, [2826], [79159]⟩,
        ⟨11171, true, false, [2826], [79159]⟩,
        ⟨11170, true, false, [2826], [79159]⟩,
        ⟨11234, false, false, [2826, 2853], []⟩,
        ⟨11137, true, false, [], [2853, 2827, 78103]⟩,
        ⟨11235, true, false, [], [2827, 78103]⟩,
        ⟨11236, true, false, [], [78103]⟩,
        ⟨11270, false, false, [], []⟩,
        ⟨11270, false, false, [], []⟩
      ]⟩,
    ⟨[78101, 5], [78101, 5], .contexts []⟩,
    ⟨[2939], [2912], .source 1534⟩,
    ⟨[2912], [2912], .contexts []⟩,
    ⟨[2939], [2912], .contexts [
        ⟨11273, false, false, [], []⟩,
        ⟨11274, false, false, [], []⟩,
        ⟨11274, false, false, [], []⟩
      ]⟩,
    ⟨[78105, 5], [78105, 5], .contexts []⟩,
    ⟨[2885, 77435], [2885, 77435], .contexts []⟩,
    ⟨[2885, 77435], [2885, 77435], .contexts []⟩,
    ⟨[77887, 9], [77887, 9], .contexts []⟩,
    ⟨[2885], [2885], .contexts []⟩,
    ⟨[2885], [2885], .contexts []⟩,
    ⟨[77887, 9], [2885, 77435], .contexts [
        ⟨11279, false, false, [], []⟩,
        ⟨11212, true, false, [], [9]⟩,
        ⟨1112, false, false, [77885], []⟩,
        ⟨1113, false, false, [77885], []⟩,
        ⟨11204, false, false, [], [3]⟩,
        ⟨11217, false, false, [], [3]⟩,
        ⟨11217, false, false, [], [3]⟩,
        ⟨2225, false, false, [2885], []⟩,
        ⟨11277, false, false, [], []⟩,
        ⟨11278, false, false, [], []⟩,
        ⟨3544, false, false, [2885], []⟩,
        ⟨11281, true, false, [], [77435]⟩,
        ⟨11280, true, false, [], [77435]⟩,
        ⟨24, true, false, [], [2885, 77435]⟩
      ]⟩,
    ⟨[2891, 77885], [2891, 77885], .contexts []⟩,
    ⟨[77885, 11], [2891, 77885], .contexts [
        ⟨11207, false, false, [], []⟩,
        ⟨11207, false, false, [], []⟩,
        ⟨11206, false, false, [2886], [77885, 11]⟩,
        ⟨11188, true, false, [2886, 2783], [11]⟩,
        ⟨6492, true, false, [2886, 2783], [11]⟩,
        ⟨11205, true, false, [2886], [5, 11]⟩,
        ⟨11205, true, false, [2886], [5, 11]⟩,
        ⟨11106, true, false, [2886], [5, 11]⟩,
        ⟨11103, true, false, [2886], [5, 11]⟩,
        ⟨1028, false, false, [2886, 78233], []⟩,
        ⟨6735, false, false, [2886], []⟩,
        ⟨11200, false, false, [2886], []⟩,
        ⟨11201, false, false, [2886, 2869], []⟩,
        ⟨11208, true, false, [], [2869, 77885]⟩,
        ⟨11209, true, false, [], [77885]⟩,
        ⟨11283, false, false, [], []⟩,
        ⟨11283, false, false, [], []⟩
      ]⟩,
    ⟨[2891, 77887], [2891, 77887], .contexts []⟩,
    ⟨[2891, 77887], [2891, 77887], .contexts []⟩,
    ⟨[77887, 11], [77887, 11], .contexts []⟩,
    ⟨[2891], [2891], .contexts [
        ⟨24, false, false, [], [2891]⟩
      ]⟩,
    ⟨[77887, 5], [77889], .contexts [
        ⟨5006, false, false, [], []⟩,
        ⟨5231, false, false, [], []⟩,
        ⟨5011, false, false, [], []⟩,
        ⟨5011, false, false, [], []⟩
      ]⟩,
    ⟨[2879, 78225], [2879, 78225], .contexts []⟩,
    ⟨[77887, 1], [2879, 78225], .contexts [
        ⟨11193, false, false, [], []⟩,
        ⟨11290, false, false, [], []⟩,
        ⟨11290, false, false, [], []⟩
      ]⟩,
    ⟨[78225], [78225], .contexts []⟩,
    ⟨[2941], [2878], .source 1535⟩,
    ⟨[78225, 5], [2941, 77891], .contexts [
        ⟨24, false, false, [2878], [2879, 78225, 5]⟩,
        ⟨11292, true, false, [], [5]⟩,
        ⟨11291, true, false, [2878], [5]⟩,
        ⟨19, true, false, [2878, 77887], [5]⟩,
        ⟨1509, true, false, [2878, 77887], [5]⟩,
        ⟨11289, false, false, [2878], [1, 5, 5]⟩,
        ⟨5010, false, false, [2878], [5, 5]⟩,
        ⟨5230, false, false, [2878], [5, 5]⟩,
        ⟨5015, false, false, [2878], [5, 5]⟩,
        ⟨5015, false, false, [2878], [5, 5]⟩,
        ⟨49, false, false, [2878, 77891], []⟩,
        ⟨11293, true, false, [], [77891]⟩
      ]⟩,
    ⟨[77887, 11], [2891, 77887], .contexts [
        ⟨11287, false, false, [], []⟩,
        ⟨11287, false, false, [], []⟩,
        ⟨11212, true, false, [], [11]⟩,
        ⟨231, false, false, [77885], []⟩,
        ⟨232, false, false, [77885], []⟩,
        ⟨11284, false, false, [], [3]⟩,
        ⟨5003, false, false, [2891], []⟩,
        ⟨11285, false, false, [], []⟩,
        ⟨11286, false, false, [], []⟩,
        ⟨11214, false, false, [2891], []⟩,
        ⟨11288, true, false, [], [77887]⟩,
        ⟨11285, false, false, [], []⟩,
        ⟨11286, false, false, [], []⟩,
        ⟨11286, false, false, [], []⟩
      ]⟩,
    ⟨[77889], [77889], .contexts []⟩,
    ⟨[2893, 77887], [2893, 77887], .contexts []⟩,
    ⟨[77887, 13], [2893, 77887], .contexts [
        ⟨11213, false, false, [], []⟩,
        ⟨11213, false, false, [], []⟩,
        ⟨11211, true, false, [2876], [13]⟩,
        ⟨1881, false, false, [2876, 77885], []⟩,
        ⟨36, false, false, [2876, 77885], []⟩,
        ⟨11212, false, false, [2876], []⟩,
        ⟨11214, false, false, [2876], []⟩,
        ⟨11216, true, false, [], [77887]⟩,
        ⟨11216, true, false, [], [77887]⟩,
        ⟨11215, true, false, [], [77887]⟩,
        ⟨11297, false, false, [], []⟩,
        ⟨11297, false, false, [], []⟩
      ]⟩,
    ⟨[2943], [2891, 2879], .source 1536⟩,
    ⟨[78225, 11], [78225, 11], .contexts []⟩,
    ⟨[2941], [2878], .contexts [
        ⟨11293, false, false, [], []⟩
      ]⟩,
    ⟨[2945], [2941, 2943], .source 1537⟩,
    ⟨[2947], [2893, 2879], .source 1538⟩,
    ⟨[2949], [2941, 2947], .source 1539⟩,
    ⟨[2951], [2948], .source 1540⟩,
    ⟨[78225, 13], [78223], .contexts [
        ⟨6562, false, false, [], []⟩
      ]⟩,
    ⟨[78223], [2951, 78221], .contexts [
        ⟨6479, true, false, [], []⟩,
        ⟨6479, true, false, [], []⟩,
        ⟨6563, true, false, [], []⟩,
        ⟨11306, true, false, [], []⟩,
        ⟨11304, false, false, [2948], [78225, 13]⟩,
        ⟨11301, false, false, [2948], [2947, 78225, 13]⟩,
        ⟨11292, true, false, [2948, 2878, 2947], [13]⟩,
        ⟨11303, false, false, [2948, 2878], [78225, 13]⟩,
        ⟨11193, true, false, [2948, 2878, 2893], [13]⟩,
        ⟨11298, true, false, [2948, 2878], [1, 13]⟩,
        ⟨190, true, false, [2948, 2878, 77887], [13]⟩,
        ⟨1587, true, false, [2948, 2878, 77887], [13]⟩,
        ⟨11291, false, false, [2948, 2878], [13, 1, 13, 13]⟩,
        ⟨6480, false, false, [2948], [1, 13, 13]⟩,
        ⟨6477, false, false, [2948], [13, 13]⟩,
        ⟨98, false, false, [2948, 78221], []⟩,
        ⟨11305, true, false, [], [78221]⟩
      ]⟩,
    ⟨[78109, 13, 3], [2779, 78107], .contexts [
        ⟨11198, false, false, [], [3]⟩,
        ⟨11198, false, false, [], [3]⟩,
        ⟨6178, true, false, [], [13, 3]⟩,
        ⟨283, false, false, [78111], [3]⟩,
        ⟨284, false, false, [78111], [3]⟩,
        ⟨11194, false, false, [], [5, 3]⟩,
        ⟨11195, false, false, [], [5, 3]⟩,
        ⟨11195, false, false, [], [5, 3]⟩,
        ⟨6067, false, false, [2779], [3]⟩,
        ⟨11196, false, false, [], [3]⟩,
        ⟨11197, false, false, [], [3]⟩,
        ⟨6180, false, false, [2779], [3]⟩,
        ⟨24, true, false, [], [2779, 78109, 3]⟩,
        ⟨11196, false, false, [], [3]⟩,
        ⟨11197, false, false, [], [3]⟩,
        ⟨11197, false, false, [], [3]⟩,
        ⟨6063, false, false, [2779], []⟩
      ]⟩,
    ⟨[2953], [2778], .source 1541⟩,
    ⟨[2778], [2778], .contexts []⟩,
    ⟨[2955], [2893, 2885], .source 1542⟩,
    ⟨[77435, 13], [77435, 13], .contexts []⟩,
    ⟨[2957], [2954], .source 1543⟩,
    ⟨[2959], [2957, 2885], .source 1544⟩,
    ⟨[2905, 78105], [2905, 78105], .contexts []⟩,
    ⟨[2961], [2905, 2829], .source 1545⟩,
    ⟨[78105, 13], [2829, 79155], .contexts [
        ⟨11237, false, false, [], []⟩
      ]⟩,
    ⟨[2829, 79155], [2829, 79155], .contexts []⟩,
    ⟨[78105, 13], [2829, 79155], .contexts [
        ⟨11317, false, false, [], []⟩,
        ⟨11318, false, false, [], []⟩,
        ⟨11318, false, false, [], []⟩
      ]⟩,
    ⟨[2963], [2960], .source 1546⟩,
    ⟨[2965], [2963, 2829], .source 1547⟩,
    ⟨[2953, 78107], [2953, 78107], .contexts []⟩,
    ⟨[78105, 1, 13, 1, 13], [2953, 2829, 79155], .contexts [
        ⟨6057, false, false, [], [13, 1, 13]⟩,
        ⟨6081, false, false, [], [13, 1, 13]⟩,
        ⟨6062, false, false, [], [13, 1, 13]⟩,
        ⟨6062, false, false, [], [13, 1, 13]⟩,
        ⟨11308, true, false, [2778], [13, 1, 13]⟩,
        ⟨1881, false, false, [2778, 78109], [1, 13]⟩,
        ⟨6187, false, false, [2778], [1, 13]⟩,
        ⟨6186, false, false, [2778], [1, 13]⟩,
        ⟨6190, false, false, [2778], [1, 13]⟩,
        ⟨11310, true, false, [], [78107, 1, 13]⟩,
        ⟨11310, true, false, [], [78107, 1, 13]⟩,
        ⟨11309, true, false, [], [78107, 1, 13]⟩,
        ⟨11322, false, false, [], [1, 13]⟩,
        ⟨11322, false, false, [], [1, 13]⟩,
        ⟨6059, false, false, [2953], [13]⟩,
        ⟨11237, false, false, [2953], []⟩
      ]⟩,
    ⟨[2967], [2953, 2829], .source 1548⟩,
    ⟨[2967, 79153], [2967, 79153], .contexts []⟩,
    ⟨[78105], [78105], .contexts []⟩,
    ⟨[2969], [2966], .source 1549⟩]

/-- Exact literal claimed equations and contextual derivations, block 177. -/
def y322TCContextRaw177 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2966], [2966], .contexts []⟩,
    ⟨[79155], [2828, 2967, 79153], .contexts [
        ⟨11319, true, false, [2828], []⟩,
        ⟨11327, false, false, [2828, 2968], [78105, 13]⟩,
        ⟨11328, false, false, [2828, 2968], [78105, 13]⟩,
        ⟨11328, false, false, [2828, 2968], [78105, 13]⟩,
        ⟨6194, true, false, [2828, 2968, 2966], [13]⟩,
        ⟨11326, true, false, [2828, 2968, 2966], [13]⟩,
        ⟨944, true, false, [2828, 2968, 2966, 78105], [13]⟩,
        ⟨11323, false, false, [2828, 2968, 2966], [1, 13, 13]⟩,
        ⟨11324, true, false, [2828, 2968, 2966], [79155, 1, 13, 13]⟩,
        ⟨10778, false, false, [2828, 2968], [13, 13]⟩,
        ⟨11325, false, false, [2828, 2968, 2966], [13, 13]⟩,
        ⟨98, false, false, [2828, 2968, 79153], []⟩,
        ⟨11327, false, true, [2828], [79153]⟩,
        ⟨11325, false, false, [2828], []⟩
      ]⟩,
    ⟨[2971], [2827, 2967], .source 1550⟩,
    ⟨[79155], [2971, 79153], .contexts [
        ⟨11329, false, false, [], []⟩,
        ⟨11232, true, false, [], [2967, 79153]⟩,
        ⟨11330, true, false, [], [79153]⟩
      ]⟩,
    ⟨[79155], [2971, 79153], .contexts [
        ⟨11331, false, false, [], []⟩
      ]⟩,
    ⟨[2973], [2970], .source 1551⟩,
    ⟨[2975], [2973, 2965], .source 1552⟩,
    ⟨[2977], [2975, 2971], .source 1553⟩,
    ⟨[2979], [2829, 2971], .source 1554⟩,
    ⟨[2981], [1369, 2979], .source 1555⟩,
    ⟨[2981, 79151], [2981, 79151], .contexts []⟩,
    ⟨[2983], [2980], .source 1556⟩,
    ⟨[2980], [2980], .contexts []⟩,
    ⟨[2979, 79153], [2981, 79151], .contexts [
        ⟨11336, false, false, [], [79153]⟩,
        ⟨11332, true, false, [2829], []⟩,
        ⟨11317, true, false, [], []⟩,
        ⟨11339, false, false, [2982], [78105, 13]⟩,
        ⟨11340, false, false, [2982], [78105, 13]⟩,
        ⟨11340, false, false, [2982], [78105, 13]⟩,
        ⟨6194, true, false, [2982, 2980], [13]⟩,
        ⟨11326, true, false, [2982, 2980], [13]⟩,
        ⟨1836, true, false, [2982, 2980, 78105], [13]⟩,
        ⟨6196, false, false, [2982, 2980], [13, 11, 13, 13]⟩,
        ⟨11237, false, false, [2982, 2980, 1369], [11, 13, 13]⟩,
        ⟨11332, false, false, [2982, 2980, 1369, 2829], [11, 13, 13]⟩,
        ⟨11336, true, false, [2982, 2980, 1369], [79153, 11, 13, 13]⟩,
        ⟨11337, true, false, [2982, 2980], [79153, 11, 13, 13]⟩,
        ⟨10774, false, false, [2982], [13, 13]⟩,
        ⟨11338, false, false, [2982, 2980], [13, 13]⟩,
        ⟨98, false, false, [2982, 79151], []⟩,
        ⟨11339, false, true, [], [79151]⟩
      ]⟩,
    ⟨[2985], [2978], .source 1557⟩,
    ⟨[2987], [2985, 2981], .source 1558⟩,
    ⟨[79153], [2987, 79151], .contexts [
        ⟨11341, false, false, [2978], []⟩,
        ⟨11338, false, false, [2978], []⟩,
        ⟨11342, true, false, [], [2981, 79151]⟩,
        ⟨11343, true, false, [], [79151]⟩
      ]⟩,
    ⟨[2989], [2971, 2987], .source 1559⟩,
    ⟨[79155], [2989, 79151], .contexts [
        ⟨11332, false, false, [], []⟩,
        ⟨11344, false, false, [2971], []⟩,
        ⟨11345, true, false, [], [79151]⟩
      ]⟩,
    ⟨[2991], [2986], .source 1560⟩,
    ⟨[2993], [2991, 2989], .source 1561⟩,
    ⟨[2987, 79151, 3], [2977, 79153], .contexts [
        ⟨11344, true, false, [], [3]⟩,
        ⟨11331, true, false, [2970], [3]⟩,
        ⟨11316, false, false, [2970, 2960], [79155, 3]⟩,
        ⟨11237, true, false, [2970, 2960, 2905], [3]⟩,
        ⟨11315, true, false, [2970, 2960], [13, 3]⟩,
        ⟨11315, true, false, [2970, 2960], [13, 3]⟩,
        ⟨11223, true, false, [2970, 2960], [13, 3]⟩,
        ⟨11220, true, false, [2970, 2960], [13, 3]⟩,
        ⟨932, false, false, [2970, 2960, 78105], []⟩,
        ⟨108, false, false, [2970, 2960, 78105], []⟩,
        ⟨11319, false, false, [2970, 2960], []⟩,
        ⟨11320, true, false, [2970], [2829, 79155]⟩,
        ⟨11321, true, false, [2970], [79155]⟩,
        ⟨11332, false, false, [2970, 2965], []⟩,
        ⟨11333, true, false, [], [2965, 2971, 79153]⟩,
        ⟨11334, true, false, [], [2971, 79153]⟩,
        ⟨11335, true, false, [], [79153]⟩
      ]⟩,
    ⟨[2995], [2991, 2977], .source 1562⟩,
    ⟨[2997], [2995, 2987], .source 1563⟩,
    ⟨[2999], [2829, 2989], .source 1564⟩,
    ⟨[2939, 78105], [2939, 78105], .contexts []⟩,
    ⟨[3001], [2939, 2999], .source 1565⟩,
    ⟨[78105, 5, 13], [3001, 79151], .contexts [
        ⟨11276, false, false, [], [13]⟩,
        ⟨11276, false, false, [], [13]⟩,
        ⟨6053, true, false, [], [5, 13]⟩,
        ⟨11271, true, false, [2912], [15, 5, 13]⟩,
        ⟨2006, false, false, [2912, 78103], [13]⟩,
        ⟨20, false, false, [2912, 78103], [13]⟩,
        ⟨6053, false, false, [2912], [13]⟩,
        ⟨6083, false, false, [2912], [13]⟩,
        ⟨6058, false, false, [2912], [13]⟩,
        ⟨6058, false, false, [2912], [13]⟩,
        ⟨6194, false, false, [2912], [13]⟩,
        ⟨11275, true, false, [], [78105, 13]⟩,
        ⟨11353, false, false, [], [13]⟩,
        ⟨11353, false, false, [], [13]⟩,
        ⟨11237, false, false, [2939], []⟩,
        ⟨11346, false, false, [2939, 2829], []⟩,
        ⟨11352, true, false, [2939], [79151]⟩,
        ⟨11354, true, false, [], [79151]⟩
      ]⟩,
    ⟨[79151, 5], [79151, 5], .contexts []⟩,
    ⟨[3003], [2998], .source 1566⟩,
    ⟨[3005], [3003, 3001], .source 1567⟩,
    ⟨[2921, 77625], [2921, 77625], .contexts []⟩,
    ⟨[2921, 77627], [2921, 77627], .contexts []⟩,
    ⟨[2921, 77627], [2921, 77627], .contexts []⟩,
    ⟨[77627, 13], [77627, 13], .contexts []⟩,
    ⟨[2920], [2920], .contexts []⟩,
    ⟨[77627, 13], [2923, 77265], .contexts [
        ⟨11362, false, false, [], []⟩,
        ⟨11361, true, false, [2920], [13]⟩,
        ⟨11360, true, false, [2920], [13]⟩,
        ⟨3759, true, false, [], [13]⟩,
        ⟨11359, true, false, [2920], [3, 13]⟩,
        ⟨11359, true, false, [2920], [3, 13]⟩,
        ⟨11247, true, false, [2920], [3, 13]⟩,
        ⟨11244, true, false, [2920], [3, 13]⟩,
        ⟨1881, false, false, [2920, 77263], []⟩,
        ⟨36, false, false, [2920, 77263], []⟩,
        ⟨9186, false, false, [2920], []⟩,
        ⟨2894, false, false, [2920], []⟩,
        ⟨11363, true, false, [], [77265]⟩,
        ⟨11363, true, false, [], [77265]⟩,
        ⟨11248, true, false, [], [77265]⟩
      ]⟩,
    ⟨[77265, 13], [2921, 77627], .contexts [
        ⟨11364, true, false, [2922], [13]⟩,
        ⟨98, false, false, [2922, 77627], []⟩,
        ⟨11248, false, true, [], [77627]⟩
      ]⟩,
    ⟨[77625, 15], [2841, 77625], .contexts [
        ⟨11252, false, false, [], []⟩,
        ⟨11252, false, false, [], []⟩,
        ⟨11150, true, false, [], [2841, 77625, 15]⟩,
        ⟨11153, true, false, [2843], [15]⟩,
        ⟨11249, true, false, [], [1, 15]⟩,
        ⟨11249, true, false, [], [1, 15]⟩,
        ⟨11251, true, false, [], [1, 15]⟩,
        ⟨3752, true, false, [], [1, 15]⟩,
        ⟨2778, false, false, [77621], []⟩,
        ⟨11159, false, false, [], []⟩,
        ⟨11158, false, false, [], []⟩,
        ⟨11161, false, false, [2841], []⟩,
        ⟨24, true, false, [], [2841, 77625]⟩,
        ⟨11156, false, false, [], []⟩,
        ⟨11157, false, false, [], []⟩,
        ⟨11157, false, false, [], []⟩
      ]⟩,
    ⟨[77627, 15], [77627, 15], .contexts []⟩,
    ⟨[77627], [77627], .contexts []⟩,
    ⟨[2843], [2843], .contexts []⟩,
    ⟨[2840], [2840], .contexts []⟩,
    ⟨[2927, 78995], [2927, 78995], .contexts []⟩,
    ⟨[3007], [2927, 1075], .source 1568⟩,
    ⟨[3009], [1753, 2931], .source 1569⟩,
    ⟨[3011], [3007, 3009], .source 1570⟩,
    ⟨[77629, 1], [77631], .contexts [
        ⟨3766, false, false, [], []⟩,
        ⟨3961, false, false, [], []⟩,
        ⟨3771, false, false, [], []⟩,
        ⟨3771, false, false, [], []⟩
      ]⟩,
    ⟨[3011, 77631, 3], [77631], .contexts [
        ⟨3766, true, false, [3011], [3]⟩,
        ⟨11374, false, false, [], [77629, 1, 3]⟩,
        ⟨11373, false, false, [3007], [77629, 1, 3]⟩,
        ⟨11266, true, false, [3007, 1753], [1, 3]⟩,
        ⟨10340, true, false, [3007], [1, 3]⟩,
        ⟨11372, false, false, [], [78995, 3, 1, 3]⟩,
        ⟨10255, true, false, [2927], [3, 1, 3]⟩,
        ⟨11371, true, false, [], [1, 3, 1, 3]⟩,
        ⟨11371, true, false, [], [1, 3, 1, 3]⟩,
        ⟨11257, true, false, [], [1, 3, 1, 3]⟩,
        ⟨11255, true, false, [], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [77629], []⟩,
        ⟨19, false, false, [77629], []⟩,
        ⟨11375, false, false, [], []⟩
      ]⟩,
    ⟨[77631], [77631], .contexts []⟩,
    ⟨[3013], [3010], .source 1571⟩,
    ⟨[3010], [3010], .contexts []⟩,
    ⟨[2933, 77267], [2933, 77267], .contexts []⟩,
    ⟨[3015], [2933, 563], .source 1572⟩,
    ⟨[3017], [3015, 2931], .source 1573⟩,
    ⟨[3017, 77631], [3017, 77631], .contexts []⟩,
    ⟨[3017, 77631], [3017, 77631], .contexts []⟩,
    ⟨[77631, 13], [77631, 13], .contexts []⟩,
    ⟨[77631, 13], [3017, 77631], .contexts [
        ⟨11385, false, false, [], []⟩,
        ⟨11375, true, false, [], [13]⟩,
        ⟨189, false, false, [77629], []⟩,
        ⟨192, false, false, [77629], []⟩,
        ⟨11264, false, false, [], [1, 13, 1]⟩,
        ⟨11380, false, false, [], [1, 13, 1]⟩,
        ⟨11380, false, false, [], [1, 13, 1]⟩,
        ⟨1222, false, false, [2933], [13, 1]⟩,
        ⟨10321, false, false, [2933], [13, 1]⟩,
        ⟨11381, true, false, [], [77267, 13, 1]⟩,
        ⟨10331, false, false, [3015], [1]⟩,
        ⟨11266, false, false, [3015], [1]⟩,
        ⟨11382, true, false, [], [77629, 1]⟩,
        ⟨3766, false, false, [3017], []⟩,
        ⟨11383, false, false, [], []⟩,
        ⟨11384, false, false, [], []⟩,
        ⟨11377, false, false, [3017], []⟩
      ]⟩,
    ⟨[2937, 77629], [2937, 77629], .contexts []⟩,
    ⟨[2937, 77631], [2937, 77631], .contexts []⟩,
    ⟨[2937, 77631], [2937, 77631], .contexts []⟩,
    ⟨[77631, 15], [77631, 15], .contexts []⟩,
    ⟨[2939, 78101], [2939, 78101], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 178. -/
def y322TCContextRaw178 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78099], [1369, 78097], .contexts [
        ⟨6047, true, false, [], []⟩,
        ⟨6047, true, false, [], []⟩,
        ⟨6090, true, false, [], []⟩,
        ⟨6212, true, false, [], []⟩,
        ⟨6211, true, false, [1382], [1]⟩,
        ⟨18, false, false, [1382, 78097], []⟩,
        ⟨6181, true, false, [], [78097]⟩,
        ⟨6208, false, false, [], []⟩,
        ⟨6161, true, false, [], [78097]⟩,
        ⟨6160, true, false, [], [78097]⟩,
        ⟨6182, true, false, [], [78097]⟩,
        ⟨6209, false, false, [], []⟩
      ]⟩,
    ⟨[3019], [2939, 1369], .source 1574⟩,
    ⟨[78101, 5, 1], [3019, 78097], .contexts [
        ⟨11272, false, false, [], [1]⟩,
        ⟨11272, false, false, [], [1]⟩,
        ⟨6051, true, false, [], [5, 1]⟩,
        ⟨11271, true, false, [2912], [13, 5, 1]⟩,
        ⟨1578, false, false, [2912, 78103], [1]⟩,
        ⟨6203, false, false, [2912], [1]⟩,
        ⟨6202, false, false, [2912], [1]⟩,
        ⟨6205, false, false, [2912], [1]⟩,
        ⟨11275, true, false, [], [78101, 1]⟩,
        ⟨11391, false, false, [], [1]⟩,
        ⟨11391, false, false, [], [1]⟩,
        ⟨6048, false, false, [2939], []⟩,
        ⟨11392, false, false, [2939], []⟩,
        ⟨11393, true, false, [], [78097]⟩
      ]⟩,
    ⟨[78097, 5], [78097, 5], .contexts []⟩,
    ⟨[78097], [78097], .contexts []⟩,
    ⟨[3021], [3018], .source 1575⟩,
    ⟨[3023], [3021, 1369], .source 1576⟩,
    ⟨[2945, 78225], [2945, 78225], .contexts []⟩,
    ⟨[2951, 78221], [2951, 78221], .contexts []⟩,
    ⟨[78223], [2951, 78221], .contexts [
        ⟨11307, false, false, [], []⟩,
        ⟨11400, false, false, [], []⟩
      ]⟩,
    ⟨[3037], [2945, 2951], .source 1583⟩,
    ⟨[3037, 78219], [3037, 78219], .contexts []⟩,
    ⟨[78225, 11, 13, 11], [3037, 78219], .contexts [
        ⟨11300, false, false, [], [13, 11]⟩,
        ⟨11300, false, false, [], [13, 11]⟩,
        ⟨11291, true, false, [2878], [11, 13, 11]⟩,
        ⟨181, false, false, [2878, 77887], [13, 11]⟩,
        ⟨182, false, false, [2878, 77887], [13, 11]⟩,
        ⟨11295, false, false, [2878], [1, 13, 11]⟩,
        ⟨11193, false, false, [2878, 2891], [13, 11]⟩,
        ⟨11299, true, false, [2878], [78225, 13, 11]⟩,
        ⟨11292, false, false, [2878, 2943], [13, 11]⟩,
        ⟨11301, true, false, [], [2943, 78225, 13, 11]⟩,
        ⟨11302, true, false, [], [78225, 13, 11]⟩,
        ⟨11399, false, false, [], [13, 11]⟩,
        ⟨11399, false, false, [], [13, 11]⟩,
        ⟨6480, false, false, [2945], [11]⟩,
        ⟨11401, false, false, [2945], [11]⟩,
        ⟨11402, true, false, [], [78221, 11]⟩,
        ⟨6474, false, false, [3037], []⟩,
        ⟨11403, false, false, [], []⟩
      ]⟩,
    ⟨[3039], [3036], .source 1584⟩,
    ⟨[3036], [3036], .contexts []⟩,
    ⟨[3041], [2949, 3037], .source 1585⟩,
    ⟨[3043], [2951, 3041], .source 1586⟩,
    ⟨[78223], [3043, 78219], .contexts [
        ⟨11401, false, false, [], []⟩,
        ⟨11400, true, false, [], []⟩,
        ⟨11400, true, false, [], []⟩,
        ⟨11401, true, false, [], []⟩,
        ⟨11306, true, false, [], []⟩,
        ⟨11405, false, false, [3038], [78225, 13]⟩,
        ⟨11406, false, false, [3038], [78225, 13]⟩,
        ⟨11406, false, false, [3038], [78225, 13]⟩,
        ⟨11292, true, false, [3038, 3036], [13]⟩,
        ⟨1836, true, false, [3038, 3036, 78225], [13]⟩,
        ⟨11404, false, false, [3038, 3036], [13, 13]⟩,
        ⟨98, false, false, [3038, 78219], []⟩,
        ⟨11405, false, true, [], [78219]⟩,
        ⟨11403, false, false, [], []⟩,
        ⟨11305, false, true, [2951], [3037, 78219]⟩,
        ⟨11407, true, false, [2951], [78219]⟩,
        ⟨11408, true, false, [], [78219]⟩
      ]⟩,
    ⟨[2959, 77435], [2959, 77435], .contexts []⟩,
    ⟨[77433], [727, 77431], .contexts [
        ⟨2221, true, false, [], []⟩,
        ⟨2221, true, false, [], []⟩,
        ⟨2337, true, false, [], []⟩,
        ⟨3554, true, false, [], []⟩,
        ⟨3553, true, false, [728], [1]⟩,
        ⟨18, false, false, [728, 77431], []⟩,
        ⟨3451, true, false, [], [77431]⟩,
        ⟨3550, false, false, [], []⟩,
        ⟨3452, true, false, [], [77431]⟩,
        ⟨3551, false, false, [], []⟩
      ]⟩,
    ⟨[3051], [2959, 727], .source 1590⟩,
    ⟨[77435, 13, 1], [3051, 77431], .contexts [
        ⟨11312, false, false, [], [1]⟩,
        ⟨11312, false, false, [], [1]⟩,
        ⟨11311, false, false, [2954], [77435, 13, 1]⟩,
        ⟨11282, true, false, [2954, 2893], [13, 1]⟩,
        ⟨11298, true, false, [2954], [9, 13, 1]⟩,
        ⟨1650, false, false, [2954, 77887], [1]⟩,
        ⟨77, false, false, [2954, 77887], [1]⟩,
        ⟨11279, false, false, [2954], [1]⟩,
        ⟨11282, false, false, [2954], [1]⟩,
        ⟨11277, false, false, [2954], [1]⟩,
        ⟨11278, false, false, [2954], [1]⟩,
        ⟨11278, false, false, [2954], [1]⟩,
        ⟨3544, false, false, [2954, 2885], [1]⟩,
        ⟨11313, true, false, [], [2885, 77435, 1]⟩,
        ⟨11314, true, false, [], [77435, 1]⟩,
        ⟨11410, false, false, [], [1]⟩,
        ⟨11410, false, false, [], [1]⟩,
        ⟨2222, false, false, [2959], []⟩,
        ⟨11411, false, false, [2959], []⟩,
        ⟨11412, true, false, [], [77431]⟩
      ]⟩,
    ⟨[3053], [3050], .source 1591⟩,
    ⟨[3055], [3053, 727], .source 1592⟩,
    ⟨[77427, 13], [3055, 77431], .contexts [
        ⟨2213, true, false, [], [13]⟩,
        ⟨2216, true, false, [], [1, 13]⟩,
        ⟨11413, true, false, [3050], [13, 1, 13]⟩,
        ⟨3422, false, false, [3050, 77435], []⟩,
        ⟨19, false, false, [3050, 77435], []⟩,
        ⟨3554, false, false, [3050], []⟩,
        ⟨11411, false, false, [3050], []⟩,
        ⟨3551, false, false, [3050], []⟩,
        ⟨3551, false, false, [3050], []⟩,
        ⟨11414, true, false, [], [727, 77431]⟩,
        ⟨11415, true, false, [], [77431]⟩
      ]⟩,
    ⟨[3057], [3054], .source 1593⟩,
    ⟨[2997, 79151], [2997, 79151], .contexts []⟩,
    ⟨[79151, 9], [79149], .contexts [
        ⟨10824, false, false, [], []⟩,
        ⟨10825, false, false, [], []⟩,
        ⟨10770, false, false, [], []⟩,
        ⟨10770, false, false, [], []⟩
      ]⟩,
    ⟨[79149, 3], [2996, 79149], .contexts [
        ⟨10771, true, false, [], [3]⟩,
        ⟨11418, true, false, [2996], [9, 3]⟩,
        ⟨11418, true, false, [2996], [9, 3]⟩,
        ⟨11351, false, false, [2996], [79151, 9, 3]⟩,
        ⟨11350, false, false, [2996], [2987, 79151, 9, 3]⟩,
        ⟨11347, false, false, [2996], [2977, 2987, 79151, 9, 3]⟩,
        ⟨11344, true, false, [2996, 2986, 2977], [9, 3]⟩,
        ⟨11349, true, false, [2996, 2986], [9, 3]⟩,
        ⟨1010, false, false, [2996, 79151], []⟩,
        ⟨77, false, false, [2996, 79151], []⟩,
        ⟨11419, false, false, [2996], []⟩
      ]⟩,
    ⟨[79149], [79149], .contexts []⟩,
    ⟨[3059], [2996], .source 1594⟩,
    ⟨[2996], [2996], .contexts []⟩,
    ⟨[79149, 3], [3059, 79149], .contexts [
        ⟨11420, false, false, [], []⟩,
        ⟨11421, false, false, [2996], []⟩,
        ⟨11423, true, false, [], [79149]⟩,
        ⟨11423, true, false, [], [79149]⟩,
        ⟨11422, true, false, [], [79149]⟩
      ]⟩,
    ⟨[3005, 79151], [3005, 79151], .contexts []⟩,
    ⟨[3005, 79149], [3005, 79149], .contexts []⟩,
    ⟨[3005, 79149], [3005, 79149], .contexts []⟩,
    ⟨[79149, 5], [3005, 79149], .contexts [
        ⟨11419, true, false, [], [5]⟩,
        ⟨1805, false, false, [79151], []⟩,
        ⟨1806, false, false, [79151], []⟩,
        ⟨11356, false, false, [], [9]⟩,
        ⟨11356, false, false, [], [9]⟩,
        ⟨11352, false, false, [2998], [79151, 5, 9]⟩,
        ⟨11346, true, false, [2998, 2829], [5, 9]⟩,
        ⟨11317, true, false, [2998], [5, 9]⟩,
        ⟨116, false, false, [2998, 78105], [9]⟩,
        ⟨117, false, false, [2998, 78105], [9]⟩,
        ⟨11355, false, false, [2998], [9]⟩,
        ⟨11357, true, false, [], [3001, 79151, 9]⟩,
        ⟨11358, true, false, [], [79151, 9]⟩,
        ⟨11425, false, false, [], [9]⟩,
        ⟨11425, false, false, [], [9]⟩,
        ⟨10771, false, false, [3005], []⟩,
        ⟨11426, false, false, [], []⟩,
        ⟨11427, false, false, [], []⟩
      ]⟩,
    ⟨[79149, 5], [79149, 5], .contexts []⟩,
    ⟨[3005], [3005], .contexts []⟩,
    ⟨[3005], [3005], .contexts []⟩,
    ⟨[77631, 9], [77633], .contexts [
        ⟨3770, false, false, [], []⟩,
        ⟨3959, false, false, [], []⟩,
        ⟨3775, false, false, [], []⟩,
        ⟨3775, false, false, [], []⟩
      ]⟩,
    ⟨[77631, 8], [77631, 9], .contexts [
        ⟨77, false, false, [77631], []⟩
      ]⟩,
    ⟨[77633], [77633], .contexts []⟩,
    ⟨[77633, 13], [77633, 13], .contexts []⟩,
    ⟨[77633, 13], [3016, 77633], .contexts [
        ⟨3770, true, false, [], [13]⟩,
        ⟨11384, true, false, [3016], [9, 13]⟩,
        ⟨11384, true, false, [3016], [9, 13]⟩,
        ⟨11383, true, false, [3016], [9, 13]⟩,
        ⟨24, false, false, [3016], [3017, 77631, 9, 13]⟩,
        ⟨11386, true, false, [3016], [9, 13]⟩,
        ⟨11385, true, false, [3016], [9, 13]⟩,
        ⟨1650, false, false, [3016, 77631], []⟩,
        ⟨11433, false, false, [3016], []⟩,
        ⟨11432, false, false, [3016], []⟩
      ]⟩,
    ⟨[3063], [3016], .source 1596⟩,
    ⟨[3063], [3063], .contexts []⟩,
    ⟨[3063], [3016], .contexts [
        ⟨11437, false, false, [], []⟩
      ]⟩,
    ⟨[3016], [3016], .contexts []⟩,
    ⟨[3063], [3016], .contexts [
        ⟨11438, false, false, [], []⟩,
        ⟨11439, false, false, [], []⟩,
        ⟨11440, false, false, [], []⟩,
        ⟨11440, false, false, [], []⟩
      ]⟩,
    ⟨[77633, 13], [3063, 77633], .contexts [
        ⟨11435, false, false, [], []⟩,
        ⟨11436, false, false, [], []⟩,
        ⟨11434, false, false, [3016], []⟩,
        ⟨11441, true, false, [], [77633]⟩
      ]⟩,
    ⟨[77631, 15, 9], [2937, 77633], .contexts [
        ⟨11390, false, false, [], [9]⟩,
        ⟨11390, false, false, [], [9]⟩,
        ⟨11375, true, false, [], [15, 9]⟩,
        ⟨199, false, false, [77629], [9]⟩,
        ⟨200, false, false, [77629], [9]⟩,
        ⟨11269, false, false, [], [1, 9]⟩,
        ⟨11387, false, false, [], [1, 9]⟩,
        ⟨11387, false, false, [], [1, 9]⟩,
        ⟨3766, false, false, [2937], [9]⟩,
        ⟨11388, false, false, [], [9]⟩,
        ⟨11389, false, false, [], [9]⟩,
        ⟨11377, false, false, [2937], [9]⟩,
        ⟨24, true, false, [], [2937, 77631, 9]⟩,
        ⟨11388, false, false, [], [9]⟩,
        ⟨11389, false, false, [], [9]⟩,
        ⟨11389, false, false, [], [9]⟩,
        ⟨3770, false, false, [2937], []⟩
      ]⟩,
    ⟨[77633, 15], [77633, 15], .contexts []⟩,
    ⟨[3065], [2936], .source 1597⟩,
    ⟨[2936], [2936], .contexts []⟩,
    ⟨[3065], [2936], .contexts [
        ⟨11445, false, false, [], []⟩,
        ⟨11446, false, false, [], []⟩,
        ⟨11446, false, false, [], []⟩
      ]⟩,
    ⟨[3023, 78097], [3023, 78097], .contexts []⟩,
    ⟨[78097, 9], [78095], .contexts [
        ⟨6091, false, false, [], []⟩,
        ⟨6092, false, false, [], []⟩,
        ⟨6041, false, false, [], []⟩,
        ⟨6041, false, false, [], []⟩
      ]⟩,
    ⟨[3023, 78095, 5], [78097, 9], .contexts [
        ⟨6042, true, false, [3023], [5]⟩,
        ⟨11448, true, false, [], [9, 5]⟩,
        ⟨11448, true, false, [], [9, 5]⟩,
        ⟨11398, false, false, [], [78097, 9, 5]⟩,
        ⟨11397, false, false, [], [1369, 78097, 9, 5]⟩,
        ⟨11396, true, false, [3018, 1369], [9, 5]⟩,
        ⟨6209, true, false, [3018], [9, 5]⟩,
        ⟨6209, true, false, [3018], [9, 5]⟩,
        ⟨11392, true, false, [3018], [9, 5]⟩,
        ⟨6212, true, false, [3018], [9, 5]⟩,
        ⟨19, true, false, [3018, 78101], [9, 5]⟩,
        ⟨1509, true, false, [3018, 78101], [9, 5]⟩,
        ⟨11394, false, false, [3018], [5, 9, 5]⟩,
        ⟨11395, true, false, [], [9, 5]⟩,
        ⟨11395, true, false, [], [9, 5]⟩,
        ⟨1672, false, false, [78097], []⟩,
        ⟨77, false, false, [78097], []⟩
      ]⟩,
    ⟨[78095, 5], [78095, 5], .contexts []⟩,
    ⟨[78095], [78095], .contexts []⟩,
    ⟨[3067], [3022], .source 1598⟩,
    ⟨[3067], [3067], .contexts []⟩,
    ⟨[3022], [3022], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 179. -/
def y322TCContextRaw179 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[3005, 79145], [3005, 79145], .contexts []⟩,
    ⟨[3005, 79145], [3005, 79145], .contexts []⟩,
    ⟨[3005, 79145, 1], [79149, 5, 1, 5, 1], .contexts [
        ⟨11457, true, false, [], [1]⟩,
        ⟨11456, true, false, [], [1]⟩,
        ⟨10765, true, false, [3005], [1]⟩,
        ⟨10768, true, false, [3005], [5, 1]⟩,
        ⟨11427, true, false, [], [1, 5, 1]⟩,
        ⟨11427, true, false, [], [1, 5, 1]⟩,
        ⟨11426, true, false, [], [1, 5, 1]⟩,
        ⟨24, false, false, [], [3005, 79149, 1, 5, 1]⟩,
        ⟨11430, false, false, [], [79149, 1, 5, 1]⟩,
        ⟨11431, false, false, [], [79149, 1, 5, 1]⟩,
        ⟨11421, true, false, [3005], [1, 5, 1]⟩,
        ⟨11428, true, false, [], [1, 5, 1]⟩,
        ⟨11429, true, false, [], [1, 5, 1]⟩,
        ⟨11429, true, false, [], [1, 5, 1]⟩
      ]⟩,
    ⟨[79145, 1], [79145, 1], .contexts []⟩,
    ⟨[3069], [3004], .source 1599⟩,
    ⟨[3004], [3004], .contexts []⟩,
    ⟨[79145, 1], [3069, 79149], .contexts [
        ⟨11459, false, false, [], []⟩,
        ⟨11458, false, false, [3004], []⟩,
        ⟨1485, false, false, [3004, 79149], []⟩,
        ⟨11421, false, false, [3004], []⟩,
        ⟨11461, true, false, [], [79149]⟩,
        ⟨11461, true, false, [], [79149]⟩,
        ⟨11460, true, false, [], [79149]⟩
      ]⟩,
    ⟨[79147], [3005, 79145], .contexts [
        ⟨10767, true, false, [], []⟩,
        ⟨10767, true, false, [], []⟩,
        ⟨10828, true, false, [], []⟩,
        ⟨10827, true, false, [], []⟩,
        ⟨11462, true, false, [3068], [1]⟩,
        ⟨18, false, false, [3068, 79145], []⟩,
        ⟨11460, false, true, [], [79145]⟩,
        ⟨11456, false, false, [], []⟩,
        ⟨11431, true, false, [], [79145]⟩,
        ⟨11430, true, false, [], [79145]⟩,
        ⟨11457, false, false, [], []⟩
      ]⟩,
    ⟨[77633, 11], [77635], .contexts [
        ⟨3774, false, false, [], []⟩,
        ⟨3958, false, false, [], []⟩,
        ⟨3778, false, false, [], []⟩,
        ⟨3778, false, false, [], []⟩
      ]⟩,
    ⟨[77633, 10], [77633, 11], .contexts [
        ⟨91, false, false, [77633], []⟩
      ]⟩,
    ⟨[77635], [77635], .contexts []⟩,
    ⟨[3063, 77633], [3063, 77633], .contexts []⟩,
    ⟨[77635, 13], [77635, 13], .contexts []⟩,
    ⟨[3017], [3062], .contexts [
        ⟨11437, true, true, [], []⟩
      ]⟩,
    ⟨[3062], [3062], .contexts []⟩,
    ⟨[3017], [3062], .contexts [
        ⟨11469, false, false, [], []⟩,
        ⟨11470, false, false, [], []⟩,
        ⟨11470, false, false, [], []⟩
      ]⟩,
    ⟨[3065, 77633], [3065, 77633], .contexts []⟩,
    ⟨[3065, 77635, 15], [77633, 10], .contexts [
        ⟨3774, true, false, [3065], [15]⟩,
        ⟨11472, true, false, [], [11, 15]⟩,
        ⟨11472, true, false, [], [11, 15]⟩,
        ⟨11447, false, false, [], [77633, 11, 15]⟩,
        ⟨11434, true, false, [2936], [11, 15]⟩,
        ⟨11432, true, false, [2936], [11, 15]⟩,
        ⟨11433, true, false, [2936], [11, 15]⟩,
        ⟨2787, true, false, [2936, 77631], [11, 15]⟩,
        ⟨11443, false, false, [2936], [15, 11, 15]⟩,
        ⟨11444, true, false, [], [11, 15]⟩,
        ⟨11444, true, false, [], [11, 15]⟩,
        ⟨3495, false, false, [77633], []⟩
      ]⟩,
    ⟨[77635, 15], [77635, 15], .contexts []⟩,
    ⟨[3064], [3064], .contexts []⟩,
    ⟨[3067, 78095], [3067, 78095], .contexts []⟩,
    ⟨[3067, 78091], [3067, 78091], .contexts []⟩,
    ⟨[78095, 5, 1, 5], [3067, 78091], .contexts [
        ⟨11451, false, false, [], [1, 5]⟩,
        ⟨11451, false, false, [], [1, 5]⟩,
        ⟨11450, false, false, [3022], [1, 5]⟩,
        ⟨11449, false, false, [3022], [1, 5]⟩,
        ⟨11452, false, false, [3022], [1, 5]⟩,
        ⟨11455, true, false, [], [78095, 1, 5]⟩,
        ⟨11455, true, false, [], [78095, 1, 5]⟩,
        ⟨11453, true, false, [], [78095, 1, 5]⟩,
        ⟨11454, true, false, [], [78095, 1, 5]⟩,
        ⟨11476, false, false, [], [1, 5]⟩,
        ⟨11476, false, false, [], [1, 5]⟩,
        ⟨6039, false, false, [3067], [5]⟩,
        ⟨6036, false, false, [3067], []⟩,
        ⟨11477, false, false, [], []⟩
      ]⟩,
    ⟨[3067, 78091], [3067, 78091], .contexts []⟩,
    ⟨[3023], [3066], .contexts [
        ⟨11453, true, true, [], []⟩
      ]⟩,
    ⟨[3066], [3066], .contexts []⟩,
    ⟨[3069, 79149], [3069, 79149], .contexts []⟩,
    ⟨[3071], [3069, 3059], .source 1600⟩,
    ⟨[3073], [3071, 3005], .source 1601⟩,
    ⟨[3073, 79141], [3073, 79141], .contexts []⟩,
    ⟨[3073, 79141], [3073, 79141], .contexts []⟩,
    ⟨[79145, 1, 3, 1, 3, 1], [3073, 79141], .contexts [
        ⟨11459, false, false, [], [3, 1, 3, 1]⟩,
        ⟨11462, false, false, [], [3, 1, 3, 1]⟩,
        ⟨11482, false, false, [], [3, 1, 3, 1]⟩,
        ⟨11482, false, false, [], [3, 1, 3, 1]⟩,
        ⟨11424, false, false, [3069], [1, 3, 1]⟩,
        ⟨11483, true, false, [], [79149, 1, 3, 1]⟩,
        ⟨10768, false, false, [3071], [3, 1]⟩,
        ⟨11463, false, false, [3071], [3, 1]⟩,
        ⟨11484, true, false, [], [79145, 3, 1]⟩,
        ⟨10761, false, false, [3073], [1]⟩,
        ⟨10758, false, false, [3073], []⟩,
        ⟨11485, false, false, [], []⟩,
        ⟨11486, false, false, [], []⟩
      ]⟩,
    ⟨[3075], [3072], .source 1602⟩,
    ⟨[3072], [3072], .contexts []⟩,
    ⟨[79141, 3], [3075, 79145], .contexts [
        ⟨11487, true, false, [3072], [3]⟩,
        ⟨7214, false, false, [3072, 79145], []⟩,
        ⟨11489, true, false, [], [79145]⟩,
        ⟨11489, true, false, [], [79145]⟩,
        ⟨11488, true, false, [], [79145]⟩
      ]⟩,
    ⟨[3017, 77635], [3017, 77635], .contexts []⟩,
    ⟨[77635, 13], [3017, 77635], .contexts [
        ⟨11468, false, false, [], []⟩,
        ⟨11468, false, false, [], []⟩,
        ⟨3774, true, false, [], [13]⟩,
        ⟨11467, true, false, [3062], [11, 13]⟩,
        ⟨11467, true, false, [3062], [11, 13]⟩,
        ⟨11442, true, false, [3062], [11, 13]⟩,
        ⟨11435, true, false, [3062], [11, 13]⟩,
        ⟨1624, false, false, [3062, 77633], []⟩,
        ⟨11465, false, false, [3062], []⟩,
        ⟨11464, false, false, [3062], []⟩,
        ⟨11466, false, false, [3062], []⟩,
        ⟨11471, true, false, [], [77635]⟩,
        ⟨11491, false, false, [], []⟩,
        ⟨11491, false, false, [], []⟩
      ]⟩,
    ⟨[77635, 1], [77637], .contexts [
        ⟨3777, false, false, [], []⟩,
        ⟨3957, false, false, [], []⟩,
        ⟨3781, false, false, [], []⟩,
        ⟨3781, false, false, [], []⟩
      ]⟩,
    ⟨[77639, 1], [77639, 1], .contexts []⟩,
    ⟨[77639], [77639], .contexts []⟩,
    ⟨[2937, 77635], [2937, 77635], .contexts []⟩,
    ⟨[2937, 77637, 15], [77635, 0], .contexts [
        ⟨3777, true, false, [2937], [15]⟩,
        ⟨11496, true, false, [], [1, 15]⟩,
        ⟨11496, true, false, [], [1, 15]⟩,
        ⟨11445, true, true, [], [77635, 1, 15]⟩,
        ⟨11475, false, false, [], [77635, 1, 15]⟩,
        ⟨11475, false, false, [], [77635, 1, 15]⟩,
        ⟨11466, true, false, [3064], [1, 15]⟩,
        ⟨11464, true, false, [3064], [1, 15]⟩,
        ⟨11465, true, false, [3064], [1, 15]⟩,
        ⟨11473, true, false, [3064], [1, 15]⟩,
        ⟨11474, true, false, [], [1, 15]⟩,
        ⟨11474, true, false, [], [1, 15]⟩,
        ⟨2778, false, false, [77635], []⟩
      ]⟩,
    ⟨[77637, 15], [77637, 15], .contexts []⟩,
    ⟨[3063, 77639], [3063, 77639], .contexts []⟩,
    ⟨[77639, 1], [3063, 77639], .contexts [
        ⟨11494, false, false, [], []⟩,
        ⟨11494, false, false, [], []⟩,
        ⟨3780, true, false, [], [1]⟩,
        ⟨3777, true, false, [], [13, 1]⟩,
        ⟨11492, true, false, [3016], [1, 13, 1]⟩,
        ⟨3725, false, false, [3016, 77635], []⟩,
        ⟨388, false, false, [3016, 77635], []⟩,
        ⟨11493, false, false, [3016], [13]⟩,
        ⟨3780, false, false, [3016], []⟩,
        ⟨3956, false, false, [3016], []⟩,
        ⟨3784, false, false, [3016], []⟩,
        ⟨3784, false, false, [3016], []⟩,
        ⟨11495, false, false, [3016], []⟩,
        ⟨11441, true, false, [], [77639]⟩,
        ⟨11499, false, false, [], []⟩,
        ⟨11499, false, false, [], []⟩
      ]⟩,
    ⟨[3063, 77643], [3063, 77643], .contexts []⟩,
    ⟨[77641], [3063, 77643], .contexts [
        ⟨3787, true, false, [], []⟩,
        ⟨3787, true, false, [], []⟩,
        ⟨3954, true, false, [], []⟩,
        ⟨3783, true, false, [], []⟩,
        ⟨11471, false, false, [3016], [77639, 15]⟩,
        ⟨11495, true, false, [3016, 3062], [15]⟩,
        ⟨3731, true, false, [3016, 3062, 77639], [15]⟩,
        ⟨11500, false, false, [3016, 3062], [15, 1, 15, 15]⟩,
        ⟨3783, false, false, [3016], [1, 15, 15]⟩,
        ⟨3786, false, false, [3016], [15, 15]⟩,
        ⟨11501, false, false, [3016, 3062], [15, 15]⟩,
        ⟨3, false, false, [3016, 77643], []⟩,
        ⟨11437, true, false, [], [77643]⟩
      ]⟩,
    ⟨[3063], [3063], .contexts []⟩,
    ⟨[3063], [3063], .contexts []⟩,
    ⟨[3065, 77637], [3065, 77637], .contexts []⟩,
    ⟨[79175], [78989, 3], .source 39652⟩,
    ⟨[78989, 3], [79175], .contexts [
        ⟨11506, true, false, [], []⟩
      ]⟩,
    ⟨[79175, 3], [78989], .contexts [
        ⟨11507, true, false, [], [3]⟩,
        ⟨35, false, false, [78989], []⟩,
        ⟨10196, false, false, [], []⟩
      ]⟩,
    ⟨[79175], [79175], .contexts []⟩,
    ⟨[78989, 3], [79175], .contexts [
        ⟨11507, false, false, [], []⟩,
        ⟨11509, false, false, [], []⟩,
        ⟨11509, false, false, [], []⟩
      ]⟩,
    ⟨[79175], [79175], .contexts []⟩,
    ⟨[2375], [2375], .contexts [
        ⟨24, false, false, [], [2375]⟩
      ]⟩,
    ⟨[2547, 78509], [2547, 78509], .contexts []⟩,
    ⟨[2547, 78509], [2547, 78509], .contexts []⟩,
    ⟨[2547], [2547], .contexts []⟩,
    ⟨[2547], [2547], .contexts []⟩,
    ⟨[2187, 77679], [2187, 77679], .contexts []⟩,
    ⟨[2187, 77679], [2187, 77679], .contexts []⟩,
    ⟨[79175, 15], [79175, 15], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 180. -/
def y322TCContextRaw180 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79175, 15], [2187, 77679], .contexts [
        ⟨11519, false, false, [], []⟩,
        ⟨11510, true, false, [], [15]⟩,
        ⟨245, false, false, [78989], []⟩,
        ⟨246, false, false, [78989], []⟩,
        ⟨10226, false, false, [], [3]⟩,
        ⟨3848, false, false, [2187], []⟩,
        ⟨11517, false, false, [], []⟩,
        ⟨11518, false, false, [], []⟩,
        ⟨7609, false, false, [2187], []⟩,
        ⟨9124, true, false, [], [77679]⟩
      ]⟩,
    ⟨[77675, 1], [77675, 1], .contexts []⟩,
    ⟨[2186], [2186], .contexts []⟩,
    ⟨[77675, 1], [2189, 79175], .contexts [
        ⟨11521, false, false, [], []⟩,
        ⟨3841, true, false, [], [1]⟩,
        ⟨3845, true, false, [], [15, 1]⟩,
        ⟨11518, true, false, [2186], [1, 15, 1]⟩,
        ⟨11518, true, false, [2186], [1, 15, 1]⟩,
        ⟨11517, true, false, [2186], [1, 15, 1]⟩,
        ⟨11520, true, false, [2186], [1, 15, 1]⟩,
        ⟨11519, true, false, [2186], [1, 15, 1]⟩,
        ⟨911, false, false, [2186, 79175], []⟩,
        ⟨11511, false, false, [2186], []⟩,
        ⟨11522, true, false, [], [79175]⟩,
        ⟨11522, true, false, [], [79175]⟩,
        ⟨9125, true, false, [], [79175]⟩
      ]⟩,
    ⟨[79177], [77675, 3], .source 39653⟩,
    ⟨[79177], [79177], .contexts []⟩,
    ⟨[77675, 3], [79177], .contexts [
        ⟨11524, true, false, [], []⟩,
        ⟨11525, false, false, [], []⟩,
        ⟨11525, false, false, [], []⟩
      ]⟩,
    ⟨[77675, 1], [2189, 79175], .contexts [
        ⟨11523, false, false, [], []⟩
      ]⟩,
    ⟨[2189, 79175], [2189, 79175], .contexts []⟩,
    ⟨[2189, 79175], [2189, 79175], .contexts []⟩,
    ⟨[3089], [2189, 2209], .source 1609⟩,
    ⟨[79177, 1], [79177, 1], .contexts []⟩,
    ⟨[3089], [3089], .contexts []⟩,
    ⟨[3089], [3089], .contexts []⟩,
    ⟨[3089], [3089], .contexts [
        ⟨24, false, false, [], [3089]⟩,
        ⟨11532, false, false, [], []⟩,
        ⟨11533, false, false, [], []⟩
      ]⟩,
    ⟨[79177, 1], [3089, 77271], .contexts [
        ⟨11531, false, false, [], []⟩,
        ⟨11526, true, false, [], [1]⟩,
        ⟨213, false, false, [77675], []⟩,
        ⟨216, false, false, [77675], []⟩,
        ⟨11521, false, false, [], [3, 1, 3]⟩,
        ⟨11527, false, false, [], [3, 1, 3]⟩,
        ⟨11528, false, false, [], [3, 1, 3]⟩,
        ⟨11529, false, false, [], [3, 1, 3]⟩,
        ⟨11529, false, false, [], [3, 1, 3]⟩,
        ⟨11508, false, false, [2189], [1, 3]⟩,
        ⟨10194, false, false, [2189], [3]⟩,
        ⟨9196, true, false, [2189, 2210], [3]⟩,
        ⟨35, false, false, [2189, 2210, 77271], []⟩,
        ⟨9197, true, false, [2189], [77271]⟩,
        ⟨11530, true, false, [], [77271]⟩,
        ⟨9807, false, false, [3089], []⟩,
        ⟨11534, true, false, [], [77271]⟩
      ]⟩,
    ⟨[3091], [3088], .source 1610⟩,
    ⟨[79177], [79177], .contexts []⟩,
    ⟨[3089, 77271], [3089, 77271], .contexts []⟩,
    ⟨[3089, 77273], [3089, 77273], .contexts []⟩,
    ⟨[3089, 77273], [3089, 77273], .contexts []⟩,
    ⟨[3089, 77273], [3089, 77273], .contexts []⟩,
    ⟨[3089, 77275], [3089, 77275], .contexts []⟩,
    ⟨[3089, 77275], [3089, 77275], .contexts []⟩,
    ⟨[3088], [3088], .contexts []⟩,
    ⟨[77275, 11], [3091, 79177], .contexts [
        ⟨11543, true, false, [3088], [11]⟩,
        ⟨11542, true, false, [3088], [11]⟩,
        ⟨1232, true, false, [], [11]⟩,
        ⟨11541, true, false, [3088], [1, 11]⟩,
        ⟨11540, true, false, [3088], [1, 11]⟩,
        ⟨11539, true, false, [3088], [1, 11]⟩,
        ⟨1229, true, false, [], [1, 11]⟩,
        ⟨11538, true, false, [3088], [11, 1, 11]⟩,
        ⟨11538, true, false, [3088], [11, 1, 11]⟩,
        ⟨11535, true, false, [3088], [11, 1, 11]⟩,
        ⟨11531, true, false, [3088], [11, 1, 11]⟩,
        ⟨1728, false, false, [3088, 79177], []⟩,
        ⟨11537, false, false, [3088], []⟩,
        ⟨11544, true, false, [], [79177]⟩,
        ⟨11544, true, false, [], [79177]⟩,
        ⟨11536, true, false, [], [79177]⟩
      ]⟩,
    ⟨[79177, 11], [3089, 77275], .contexts [
        ⟨11545, true, false, [3090], [11]⟩,
        ⟨90, false, false, [3090, 77275], []⟩,
        ⟨11536, false, true, [], [77275]⟩
      ]⟩,
    ⟨[79179], [78989, 7], .source 39654⟩,
    ⟨[79179], [79179], .contexts []⟩,
    ⟨[79179], [79179], .contexts []⟩,
    ⟨[79181], [78989, 13], .source 39655⟩,
    ⟨[78989, 13], [79181], .contexts [
        ⟨11550, true, false, [], []⟩
      ]⟩,
    ⟨[79181], [79181], .contexts []⟩,
    ⟨[79181], [79181], .contexts []⟩,
    ⟨[78989, 13], [79181], .contexts [
        ⟨11551, false, false, [], []⟩,
        ⟨11552, false, false, [], []⟩,
        ⟨11553, false, false, [], []⟩,
        ⟨11553, false, false, [], []⟩
      ]⟩,
    ⟨[3093], [2191, 2383], .source 1611⟩,
    ⟨[3093, 78809], [3093, 78809], .contexts [
        ⟨9627, false, false, [3093], []⟩
      ]⟩,
    ⟨[3093], [3093], .contexts []⟩,
    ⟨[3093], [3093], .contexts []⟩,
    ⟨[3093], [3093], .contexts [
        ⟨24, false, false, [], [3093]⟩,
        ⟨11557, false, false, [], []⟩,
        ⟨11558, false, false, [], []⟩
      ]⟩,
    ⟨[3093, 78809], [3093, 78809], .contexts [
        ⟨11559, true, false, [], [78809]⟩
      ]⟩,
    ⟨[3095], [3092], .source 1612⟩,
    ⟨[79181, 11], [79181, 11], .contexts []⟩,
    ⟨[79181, 11], [77149], .contexts [
        ⟨11562, false, false, [], []⟩,
        ⟨11554, true, false, [], [11]⟩,
        ⟨137, false, false, [78989], []⟩,
        ⟨138, false, false, [78989], []⟩,
        ⟨10222, false, false, [], [13]⟩,
        ⟨8494, false, false, [], []⟩,
        ⟨701, false, false, [], []⟩,
        ⟨477, false, false, [], []⟩,
        ⟨477, false, false, [], []⟩,
        ⟨10510, false, false, [], []⟩,
        ⟨10511, false, false, [], []⟩
      ]⟩,
    ⟨[79183], [78745, 5], .source 39656⟩,
    ⟨[78745, 5], [79183], .contexts [
        ⟨11564, true, false, [], []⟩
      ]⟩,
    ⟨[79183, 5], [78745], .contexts [
        ⟨11565, true, false, [], [5]⟩,
        ⟨49, false, false, [78745], []⟩,
        ⟨9346, false, false, [], []⟩
      ]⟩,
    ⟨[79183], [79183], .contexts []⟩,
    ⟨[78745, 5], [79183], .contexts [
        ⟨11565, false, false, [], []⟩,
        ⟨11567, false, false, [], []⟩,
        ⟨11567, false, false, [], []⟩
      ]⟩,
    ⟨[79183], [79183], .contexts []⟩,
    ⟨[3097], [2401, 2403], .source 1613⟩,
    ⟨[3099], [3097, 2211], .source 1614⟩,
    ⟨[3099, 78825], [3099, 78825], .contexts []⟩,
    ⟨[3099, 78825], [3099, 78825], .contexts []⟩,
    ⟨[79183, 3], [79183, 3], .contexts []⟩,
    ⟨[79183, 3], [3099, 78825], .contexts [
        ⟨11574, false, false, [], []⟩,
        ⟨11568, true, false, [], [3]⟩,
        ⟨264, false, false, [78745], []⟩,
        ⟨267, false, false, [78745], []⟩,
        ⟨9825, false, false, [], [5, 3, 5]⟩,
        ⟨9810, false, false, [2401], [3, 5]⟩,
        ⟨11570, true, false, [], [77271, 3, 5]⟩,
        ⟨9196, false, false, [3097], [5]⟩,
        ⟨11571, true, false, [], [77143, 5]⟩,
        ⟨9644, false, false, [3099], []⟩,
        ⟨11572, false, false, [], []⟩,
        ⟨11573, false, false, [], []⟩,
        ⟨24, true, false, [], [3099, 78825]⟩
      ]⟩,
    ⟨[3101], [3098], .source 1615⟩,
    ⟨[79183, 3], [3099, 78825], .contexts [
        ⟨11574, false, false, [], []⟩,
        ⟨11575, false, false, [], []⟩,
        ⟨11572, false, false, [], []⟩,
        ⟨11573, false, false, [], []⟩,
        ⟨11573, false, false, [], []⟩
      ]⟩,
    ⟨[3103], [3099, 2191], .source 1616⟩,
    ⟨[3105], [3103, 2711], .source 1617⟩,
    ⟨[79183], [79183], .contexts []⟩,
    ⟨[3107], [3104], .source 1618⟩,
    ⟨[3104], [3104], .contexts []⟩,
    ⟨[3109], [3099, 2187], .source 1619⟩]

/-- Exact literal claimed equations and contextual derivations, block 181. -/
def y322TCContextRaw181 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[3111], [1299, 1759], .source 1620⟩,
    ⟨[3113], [3109, 3111], .source 1621⟩,
    ⟨[77321, 15], [77321, 15], .contexts []⟩,
    ⟨[3115], [3112], .source 1622⟩,
    ⟨[3115], [3112], .contexts [
        ⟨11587, false, false, [], []⟩
      ]⟩,
    ⟨[3112], [3112], .contexts []⟩,
    ⟨[77321, 15], [3115, 79183], .contexts [
        ⟨11586, false, false, [], []⟩,
        ⟨11585, false, false, [3112], [77321, 15]⟩,
        ⟨11584, false, false, [3112, 3109], [77321, 15]⟩,
        ⟨7574, true, false, [3112, 3109, 1299], [15]⟩,
        ⟨5724, true, false, [3112, 3109], [15]⟩,
        ⟨11583, false, false, [3112], [77685, 3, 15]⟩,
        ⟨9655, true, false, [3112, 3099], [3, 15]⟩,
        ⟨11577, true, false, [3112], [15, 3, 15]⟩,
        ⟨2767, false, false, [3112, 79183], []⟩,
        ⟨11580, false, false, [3112], []⟩,
        ⟨11569, false, false, [3112], []⟩,
        ⟨11589, true, false, [], [79183]⟩,
        ⟨11589, true, false, [], [79183]⟩,
        ⟨11588, true, false, [], [79183]⟩
      ]⟩,
    ⟨[3113], [3114], .contexts [
        ⟨11587, true, true, [], []⟩
      ]⟩,
    ⟨[3115, 79183], [3115, 79183], .contexts []⟩,
    ⟨[78745, 15], [78745, 15], .contexts []⟩,
    ⟨[3114], [3114], .contexts []⟩,
    ⟨[78745, 15], [3113, 77319], .contexts [
        ⟨11593, false, false, [], []⟩,
        ⟨11566, true, false, [], [15]⟩,
        ⟨11592, true, false, [3114], [5, 15]⟩,
        ⟨11592, true, false, [3114], [5, 15]⟩,
        ⟨11590, true, false, [3114], [5, 15]⟩,
        ⟨11586, true, false, [3114], [5, 15]⟩,
        ⟨3532, false, false, [3114, 77321], []⟩,
        ⟨50, false, false, [3114, 77321], []⟩,
        ⟨7580, false, false, [3114], []⟩,
        ⟨7585, false, false, [3114], []⟩,
        ⟨11594, true, false, [], [77319]⟩,
        ⟨11594, true, false, [], [77319]⟩,
        ⟨11591, true, false, [], [77319]⟩
      ]⟩,
    ⟨[3113, 77319], [3113, 77319], .contexts []⟩,
    ⟨[3113, 77319], [3113, 77319], .contexts []⟩,
    ⟨[77317, 15], [77317, 15], .contexts []⟩,
    ⟨[3117], [3115, 2401], .source 1623⟩,
    ⟨[77317, 15], [3117, 78431], .contexts [
        ⟨11598, false, false, [], []⟩,
        ⟨1291, true, false, [], [15]⟩,
        ⟨11597, true, false, [3112], [3, 15]⟩,
        ⟨11597, true, false, [3112], [3, 15]⟩,
        ⟨11596, true, false, [3112], [3, 15]⟩,
        ⟨11595, true, false, [3112], [3, 15]⟩,
        ⟨11593, true, false, [3112], [3, 15]⟩,
        ⟨1893, false, false, [3112, 78745], []⟩,
        ⟨36, false, false, [3112, 78745], []⟩,
        ⟨9825, false, false, [3112], []⟩,
        ⟨9814, false, false, [3112, 2401], []⟩,
        ⟨11588, true, false, [], [2401, 78431]⟩,
        ⟨11599, true, false, [], [78431]⟩
      ]⟩,
    ⟨[3119], [3116], .source 1624⟩,
    ⟨[78431, 15], [3119, 77317], .contexts [
        ⟨11600, true, false, [3116], [15]⟩,
        ⟨3, false, false, [3116, 77317], []⟩,
        ⟨11601, true, false, [], [77317]⟩
      ]⟩,
    ⟨[3117, 78431], [3117, 78431], .contexts []⟩,
    ⟨[78431, 1], [78431, 1], .contexts []⟩,
    ⟨[3116], [3116], .contexts []⟩,
    ⟨[3119], [3116], .contexts [
        ⟨11601, false, false, [], []⟩,
        ⟨11605, false, false, [], []⟩,
        ⟨11605, false, false, [], []⟩
      ]⟩,
    ⟨[78431, 1], [3119, 77313], .contexts [
        ⟨11604, false, false, [], []⟩,
        ⟨11603, true, false, [3116], [1]⟩,
        ⟨11603, true, false, [3116], [1]⟩,
        ⟨11600, true, false, [3116], [1]⟩,
        ⟨11598, true, false, [3116], [1]⟩,
        ⟨17, false, false, [3116, 77317], []⟩,
        ⟨21, false, false, [3116, 77317], []⟩,
        ⟨1391, false, false, [3116], [15]⟩,
        ⟨1392, false, false, [3116], [15]⟩,
        ⟨1287, false, false, [3116], [15]⟩,
        ⟨1287, false, false, [3116], [15]⟩,
        ⟨1393, false, false, [3116], []⟩,
        ⟨1394, false, false, [3116], []⟩,
        ⟨1283, false, false, [3116], []⟩,
        ⟨1283, false, false, [3116], []⟩,
        ⟨7616, false, false, [3116], []⟩,
        ⟨11606, true, false, [], [77313]⟩
      ]⟩,
    ⟨[3117], [3118], .contexts [
        ⟨11601, true, true, [], []⟩
      ]⟩,
    ⟨[3119, 77313], [3119, 77313], .contexts []⟩,
    ⟨[3119, 77313], [3119, 77313], .contexts []⟩,
    ⟨[78431, 1], [3119, 77313], .contexts [
        ⟨11604, false, false, [], []⟩,
        ⟨11607, false, false, [], []⟩,
        ⟨11609, false, false, [], []⟩,
        ⟨11610, false, false, [], []⟩,
        ⟨11610, false, false, [], []⟩
      ]⟩,
    ⟨[3121], [2403, 3091], .source 1625⟩,
    ⟨[3117], [3118], .contexts [
        ⟨11608, false, false, [], []⟩
      ]⟩,
    ⟨[3123], [3117, 3121], .source 1626⟩,
    ⟨[78429], [2399, 77265], .contexts [
        ⟨9799, false, false, [], []⟩,
        ⟨9798, false, false, [], []⟩
      ]⟩,
    ⟨[3127], [2403, 2401], .source 1628⟩,
    ⟨[3129], [3127, 3119], .source 1629⟩,
    ⟨[77313, 9], [3118, 3129, 77313], .contexts [
        ⟨11611, true, false, [3118], [9]⟩,
        ⟨786, false, false, [3118, 78431], []⟩,
        ⟨788, false, false, [3118, 78431], []⟩,
        ⟨7926, false, false, [3118], [1, 9, 1]⟩,
        ⟨11615, false, false, [3118], [1, 9, 1]⟩,
        ⟨9798, false, false, [3118], [1, 9, 1]⟩,
        ⟨9798, false, false, [3118], [1, 9, 1]⟩,
        ⟨2899, false, false, [3118, 2399], [9, 1]⟩,
        ⟨9809, true, false, [3118], [77265, 9, 1]⟩,
        ⟨9801, false, false, [3118, 2403], [1]⟩,
        ⟨11616, true, false, [3118], [78431, 1]⟩,
        ⟨11607, false, false, [3118, 3127], []⟩,
        ⟨11617, true, false, [3118], [77313]⟩,
        ⟨7616, false, false, [3118, 3129], []⟩
      ]⟩,
    ⟨[3131], [3117, 3129], .source 1630⟩,
    ⟨[77313, 11], [77313, 11], .contexts []⟩,
    ⟨[3118], [3118], .contexts []⟩,
    ⟨[3117], [3118], .contexts [
        ⟨11613, false, false, [], []⟩,
        ⟨11621, false, false, [], []⟩,
        ⟨11621, false, false, [], []⟩
      ]⟩,
    ⟨[77313, 11], [3117, 78435], .contexts [
        ⟨11620, false, false, [], []⟩,
        ⟨11611, true, false, [3118], [11]⟩,
        ⟨181, false, false, [3118, 78431], []⟩,
        ⟨182, false, false, [3118, 78431], []⟩,
        ⟨9818, false, false, [3118], [1]⟩,
        ⟨9838, false, false, [3118], []⟩,
        ⟨7922, false, false, [3118], []⟩,
        ⟨7765, false, false, [3118], []⟩,
        ⟨7765, false, false, [3118], []⟩,
        ⟨9841, false, false, [3118], []⟩,
        ⟨11622, true, false, [], [78435]⟩
      ]⟩,
    ⟨[3117, 78435], [3117, 78435], .contexts []⟩,
    ⟨[3117, 78435], [3117, 78435], .contexts []⟩,
    ⟨[78437, 11], [78437, 11], .contexts []⟩,
    ⟨[78437, 11], [3119, 77311], .contexts [
        ⟨11626, false, false, [], []⟩,
        ⟨7764, true, false, [], [11]⟩,
        ⟨11625, true, false, [3116], [13, 11]⟩,
        ⟨11625, true, false, [3116], [13, 11]⟩,
        ⟨11624, true, false, [3116], [13, 11]⟩,
        ⟨11623, true, false, [3116], [13, 11]⟩,
        ⟨11620, true, false, [3116], [13, 11]⟩,
        ⟨1060, false, false, [3116, 77313], []⟩,
        ⟨7626, false, false, [3116], []⟩,
        ⟨7625, false, false, [3116], []⟩,
        ⟨7628, false, false, [3116], []⟩,
        ⟨11606, true, false, [], [77311]⟩
      ]⟩,
    ⟨[3119, 77311], [3119, 77311], .contexts []⟩,
    ⟨[3119, 77307], [3119, 77307], .contexts []⟩,
    ⟨[77307, 1], [3117, 78437], .contexts [
        ⟨11629, true, false, [3118], [1]⟩,
        ⟨1274, true, false, [], [1]⟩,
        ⟨1278, true, false, [], [11, 1]⟩,
        ⟨11628, true, false, [3118], [1, 11, 1]⟩,
        ⟨11628, true, false, [3118], [1, 11, 1]⟩,
        ⟨11627, true, false, [3118], [1, 11, 1]⟩,
        ⟨11626, true, false, [3118], [1, 11, 1]⟩,
        ⟨1068, false, false, [3118, 78437], []⟩,
        ⟨9847, false, false, [3118], []⟩,
        ⟨11622, true, false, [], [78437]⟩
      ]⟩,
    ⟨[79185], [77271, 7], .source 39657⟩,
    ⟨[77271, 7], [79185], .contexts [
        ⟨11631, true, false, [], []⟩
      ]⟩,
    ⟨[2211], [2211], .contexts [
        ⟨24, false, false, [], [2211]⟩
      ]⟩,
    ⟨[79187], [77271, 13], .source 39658⟩,
    ⟨[77271, 13], [79187], .contexts [
        ⟨11634, true, false, [], []⟩
      ]⟩,
    ⟨[77271, 13], [79187], .contexts [
        ⟨11635, false, false, [], []⟩
      ]⟩,
    ⟨[79187], [79187], .contexts []⟩,
    ⟨[79187], [79187], .contexts []⟩,
    ⟨[77271, 13], [79187], .contexts [
        ⟨11636, false, false, [], []⟩,
        ⟨11637, false, false, [], []⟩,
        ⟨11638, false, false, [], []⟩,
        ⟨11638, false, false, [], []⟩
      ]⟩,
    ⟨[3135], [563, 2931], .source 1632⟩,
    ⟨[79187, 9], [79187, 9], .contexts []⟩,
    ⟨[77629], [77629], .contexts []⟩,
    ⟨[79187, 9], [3135, 77629], .contexts [
        ⟨11641, false, false, [], []⟩,
        ⟨11639, true, false, [], [9]⟩,
        ⟨130, false, false, [77271], []⟩,
        ⟨131, false, false, [77271], []⟩,
        ⟨1408, false, false, [], [13]⟩,
        ⟨10322, false, false, [], [13]⟩,
        ⟨10320, false, false, [], [13]⟩,
        ⟨10320, false, false, [], [13]⟩,
        ⟨10331, false, false, [563], []⟩,
        ⟨11266, false, false, [563], []⟩,
        ⟨11640, true, false, [], [77629]⟩,
        ⟨11642, false, false, [3135], []⟩,
        ⟨24, true, false, [], [3135, 77629]⟩
      ]⟩,
    ⟨[79187], [79187], .contexts []⟩,
    ⟨[79189], [77271, 15], .source 39659⟩,
    ⟨[77271, 15], [79189], .contexts [
        ⟨11645, true, false, [], []⟩
      ]⟩,
    ⟨[79189], [79189], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 182. -/
def y322TCContextRaw182 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79189], [79189], .contexts []⟩,
    ⟨[3145], [2211, 1887], .source 1637⟩,
    ⟨[3145], [3145], .contexts []⟩,
    ⟨[3145], [3145], .contexts []⟩,
    ⟨[77271, 5], [2405, 78431], .contexts [
        ⟨9812, false, false, [], []⟩
      ]⟩,
    ⟨[2405, 78431], [2405, 78431], .contexts []⟩,
    ⟨[2405, 78431], [2405, 78431], .contexts []⟩,
    ⟨[3149], [2405, 3119], .source 1639⟩,
    ⟨[3151], [3148], .source 1640⟩,
    ⟨[77317, 5], [3151, 79189], .contexts [
        ⟨24, false, false, [3148], [3149, 77317, 5]⟩,
        ⟨7602, true, false, [], [5]⟩,
        ⟨11655, false, false, [3148], [77317, 5]⟩,
        ⟨11602, true, false, [3148, 2405], [5]⟩,
        ⟨11654, true, false, [3148], [15, 5]⟩,
        ⟨11654, true, false, [3148], [15, 5]⟩,
        ⟨11653, true, false, [3148], [15, 5]⟩,
        ⟨11652, true, false, [3148], [15, 5]⟩,
        ⟨51, true, false, [3148, 77271], [5]⟩,
        ⟨48, true, false, [3148, 77271], [5]⟩,
        ⟨11646, false, false, [3148], [5, 5]⟩,
        ⟨11647, false, false, [3148], [5, 5]⟩,
        ⟨11648, false, false, [3148], [5, 5]⟩,
        ⟨11648, false, false, [3148], [5, 5]⟩,
        ⟨49, false, false, [3148, 79189], []⟩,
        ⟨11656, true, false, [], [79189]⟩
      ]⟩,
    ⟨[79197], [79015, 11], .source 39663⟩,
    ⟨[79197], [79197], .contexts []⟩,
    ⟨[79197], [79197], .contexts []⟩,
    ⟨[79015, 7, 11], [77145], .contexts [
        ⟨10356, false, false, [], [11]⟩,
        ⟨10356, false, false, [], [11]⟩,
        ⟨10354, true, false, [], [7, 11]⟩,
        ⟨10354, true, false, [], [7, 11]⟩,
        ⟨10353, false, false, [], [7, 11]⟩,
        ⟨1809, false, false, [78987], [11]⟩,
        ⟨1810, false, false, [78987], [11]⟩,
        ⟨10355, false, false, [], [9, 11]⟩,
        ⟨9192, false, false, [], [11]⟩,
        ⟨708, false, false, [], [11]⟩,
        ⟨467, false, false, [], [11]⟩,
        ⟨467, false, false, [], [11]⟩,
        ⟨9641, false, false, [], [11]⟩,
        ⟨9642, false, false, [], [11]⟩,
        ⟨708, false, false, [], [11]⟩,
        ⟨467, false, false, [], [11]⟩,
        ⟨467, false, false, [], [11]⟩,
        ⟨10203, false, false, [], []⟩,
        ⟨706, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩
      ]⟩,
    ⟨[79197, 7], [79197, 7], .contexts []⟩,
    ⟨[79197, 7], [77145], .contexts [
        ⟨11662, false, false, [], []⟩,
        ⟨11660, true, false, [], [7]⟩,
        ⟨11660, true, false, [], [7]⟩,
        ⟨11659, true, false, [], [7]⟩,
        ⟨11658, false, false, [], [7]⟩,
        ⟨1088, false, false, [79015], []⟩,
        ⟨1089, false, false, [79015], []⟩,
        ⟨11661, false, false, [], []⟩,
        ⟨470, false, false, [], []⟩,
        ⟨10468, false, false, [], []⟩,
        ⟨10469, false, false, [], []⟩
      ]⟩,
    ⟨[77145, 7], [79197], .contexts [
        ⟨11663, true, false, [], [7]⟩,
        ⟨62, false, false, [79197], []⟩,
        ⟨11660, false, false, [], []⟩
      ]⟩,
    ⟨[79203], [77145, 13], .source 39666⟩,
    ⟨[77145, 13], [79203], .contexts [
        ⟨11665, true, false, [], []⟩
      ]⟩,
    ⟨[77145, 13], [79203], .contexts [
        ⟨11666, false, false, [], []⟩
      ]⟩,
    ⟨[79203], [79203], .contexts []⟩,
    ⟨[79203], [79203], .contexts []⟩,
    ⟨[79203, 11], [79027], .contexts [
        ⟨11669, true, false, [], [11]⟩,
        ⟨11669, true, false, [], [11]⟩,
        ⟨11668, true, false, [], [11]⟩,
        ⟨11667, true, false, [], [11]⟩,
        ⟨137, false, false, [77145], []⟩,
        ⟨138, false, false, [77145], []⟩,
        ⟨707, false, false, [], [13]⟩,
        ⟨708, false, false, [], [13]⟩,
        ⟨467, false, false, [], [13]⟩,
        ⟨467, false, false, [], [13]⟩,
        ⟨10445, false, false, [], []⟩,
        ⟨10446, false, false, [], []⟩,
        ⟨10447, false, false, [], []⟩,
        ⟨10447, false, false, [], []⟩,
        ⟨10452, false, false, [], []⟩,
        ⟨1118, true, false, [], [79027]⟩
      ]⟩,
    ⟨[79203], [79203], .contexts []⟩,
    ⟨[79205], [77675, 11], .source 39667⟩,
    ⟨[77675, 11], [79205], .contexts [
        ⟨11672, true, false, [], []⟩
      ]⟩,
    ⟨[79205, 11], [77675], .contexts [
        ⟨11673, true, false, [], [11]⟩,
        ⟨90, false, false, [77675], []⟩,
        ⟨3840, false, false, [], []⟩
      ]⟩,
    ⟨[79205], [79205], .contexts []⟩,
    ⟨[79205], [79205], .contexts []⟩,
    ⟨[77675, 11], [79205], .contexts [
        ⟨11673, false, false, [], []⟩,
        ⟨11675, false, false, [], []⟩,
        ⟨11676, false, false, [], []⟩,
        ⟨11676, false, false, [], []⟩
      ]⟩,
    ⟨[79205, 3], [79205, 3], .contexts []⟩,
    ⟨[79205, 3], [3089, 77275], .contexts [
        ⟨11678, false, false, [], []⟩,
        ⟨11677, true, false, [], [3]⟩,
        ⟨335, false, false, [77675], []⟩,
        ⟨336, false, false, [77675], []⟩,
        ⟨11526, false, false, [], [11]⟩,
        ⟨11546, false, false, [], []⟩,
        ⟨11542, false, false, [], []⟩,
        ⟨11543, false, false, [], []⟩,
        ⟨11543, false, false, [], []⟩,
        ⟨9831, false, false, [3089], []⟩,
        ⟨11534, true, false, [], [77275]⟩
      ]⟩,
    ⟨[1777, 79205], [1777, 79205], .contexts []⟩,
    ⟨[1777, 79205], [1777, 79205], .contexts []⟩,
    ⟨[79205, 5], [79205, 5], .contexts []⟩,
    ⟨[79205], [79205], .contexts []⟩,
    ⟨[1777], [1777], .contexts [
        ⟨24, false, false, [], [1777]⟩
      ]⟩,
    ⟨[79207], [79205, 1], .source 39668⟩,
    ⟨[79205, 1], [79207], .contexts [
        ⟨11685, true, false, [], []⟩
      ]⟩,
    ⟨[79207, 1], [79205], .contexts [
        ⟨11686, true, false, [], [1]⟩,
        ⟨18, false, false, [79205], []⟩,
        ⟨11676, false, false, [], []⟩
      ]⟩,
    ⟨[79207], [79207], .contexts []⟩,
    ⟨[79207], [79207], .contexts []⟩,
    ⟨[79205, 1], [79207], .contexts [
        ⟨11686, false, false, [], []⟩,
        ⟨11688, false, false, [], []⟩,
        ⟨11689, false, false, [], []⟩,
        ⟨11689, false, false, [], []⟩
      ]⟩,
    ⟨[3153], [3089, 2211], .source 1641⟩,
    ⟨[3153, 77147], [3153, 77147], .contexts []⟩,
    ⟨[3153, 77147], [3153, 77147], .contexts []⟩,
    ⟨[79207, 3], [79207, 3], .contexts []⟩,
    ⟨[79207, 3], [3153, 77147], .contexts [
        ⟨11694, false, false, [], []⟩,
        ⟨11690, true, false, [], [3]⟩,
        ⟨1824, false, false, [79205], []⟩,
        ⟨1826, false, false, [79205], []⟩,
        ⟨11678, false, false, [], [1, 3, 1]⟩,
        ⟨11679, false, false, [], [1, 3, 1]⟩,
        ⟨11542, false, false, [], [1, 3, 1]⟩,
        ⟨11543, false, false, [], [1, 3, 1]⟩,
        ⟨11543, false, false, [], [1, 3, 1]⟩,
        ⟨1234, false, false, [3089], [3, 1]⟩,
        ⟨11539, false, false, [], [3, 1]⟩,
        ⟨11540, false, false, [], [3, 1]⟩,
        ⟨11541, false, false, [], [3, 1]⟩,
        ⟨9205, false, false, [3089], [1]⟩,
        ⟨11691, true, false, [], [77145, 1]⟩,
        ⟨469, false, false, [3153], []⟩,
        ⟨11692, false, false, [], []⟩,
        ⟨11693, false, false, [], []⟩,
        ⟨8473, false, false, [3153], []⟩
      ]⟩,
    ⟨[3153], [3153], .contexts []⟩,
    ⟨[3153], [3153], .contexts []⟩,
    ⟨[3153], [3153], .contexts [
        ⟨24, false, false, [], [3153]⟩,
        ⟨11696, false, false, [], []⟩,
        ⟨11697, false, false, [], []⟩
      ]⟩,
    ⟨[79207, 3], [3153, 77147], .contexts [
        ⟨11695, false, false, [], []⟩,
        ⟨11698, true, false, [], [77147]⟩
      ]⟩,
    ⟨[3155], [3152], .source 1642⟩,
    ⟨[77147, 3], [3155, 79207], .contexts [
        ⟨11699, true, false, [3152], [3]⟩,
        ⟨35, false, false, [3152, 79207], []⟩,
        ⟨11700, true, false, [], [79207]⟩
      ]⟩,
    ⟨[1777, 79207], [1777, 79207], .contexts []⟩,
    ⟨[1777, 79207], [1777, 79207], .contexts []⟩,
    ⟨[79207, 5], [79207, 5], .contexts []⟩,
    ⟨[79207, 5], [1777, 79207], .contexts [
        ⟨11704, false, false, [], []⟩,
        ⟨11690, true, false, [], [5]⟩,
        ⟨165, false, false, [79205], []⟩,
        ⟨166, false, false, [79205], []⟩,
        ⟨11682, false, false, [], [1]⟩,
        ⟨11682, false, false, [], [1]⟩,
        ⟨11677, true, false, [], [5, 1]⟩,
        ⟨1083, false, false, [77675], [1]⟩,
        ⟨1084, false, false, [77675], [1]⟩,
        ⟨7636, false, false, [], [11, 1]⟩,
        ⟨11673, false, false, [1777], [1]⟩,
        ⟨11680, false, false, [], [1]⟩,
        ⟨11681, false, false, [], [1]⟩,
        ⟨11683, false, false, [1777], [1]⟩,
        ⟨11684, true, false, [], [79205, 1]⟩,
        ⟨11680, false, false, [], [1]⟩,
        ⟨11681, false, false, [], [1]⟩,
        ⟨11681, false, false, [], [1]⟩,
        ⟨11686, false, false, [1777], []⟩,
        ⟨11702, false, false, [], []⟩,
        ⟨11703, false, false, [], []⟩
      ]⟩,
    ⟨[79207], [79207], .contexts []⟩,
    ⟨[79207, 5], [1777, 79207], .contexts [
        ⟨11705, false, false, [], []⟩,
        ⟨11706, false, false, [1777], []⟩,
        ⟨11684, true, false, [], [79207]⟩
      ]⟩,
    ⟨[79205, 11], [77675], .contexts [
        ⟨11674, false, false, [], []⟩,
        ⟨3933, false, false, [], []⟩,
        ⟨3840, false, false, [], []⟩,
        ⟨3840, false, false, [], []⟩
      ]⟩,
    ⟨[79207, 11], [79207, 11], .contexts []⟩,
    ⟨[2189, 79175], [2189, 79175], .contexts [
        ⟨11511, false, false, [2189], []⟩
      ]⟩,
    ⟨[2189, 79175], [2189, 79175], .contexts [
        ⟨24, true, false, [], [2189, 79175]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 183. -/
def y322TCContextRaw183 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79207, 3], [3153, 77147], .contexts [
        ⟨11694, false, false, [], []⟩,
        ⟨11699, false, false, [], []⟩,
        ⟨11692, false, false, [], []⟩,
        ⟨11693, false, false, [], []⟩,
        ⟨11693, false, false, [], []⟩
      ]⟩,
    ⟨[3157], [3153, 2007], .source 1643⟩,
    ⟨[3159], [3157, 3155], .source 1644⟩,
    ⟨[79207, 9], [79207, 9], .contexts []⟩,
    ⟨[3161], [3158], .source 1645⟩,
    ⟨[3158], [3158], .contexts []⟩,
    ⟨[79209], [79207, 13], .source 39669⟩,
    ⟨[79207, 13], [79209], .contexts [
        ⟨11718, true, false, [], []⟩
      ]⟩,
    ⟨[79209, 13], [79207], .contexts [
        ⟨11719, true, false, [], [13]⟩,
        ⟨98, false, false, [79207], []⟩,
        ⟨11689, false, false, [], []⟩
      ]⟩,
    ⟨[79209], [79209], .contexts []⟩,
    ⟨[79209], [79209], .contexts []⟩,
    ⟨[79207, 13], [79209], .contexts [
        ⟨11719, false, false, [], []⟩,
        ⟨11721, false, false, [], []⟩,
        ⟨11722, false, false, [], []⟩,
        ⟨11722, false, false, [], []⟩
      ]⟩,
    ⟨[3153, 77149], [3153, 77149], .contexts []⟩,
    ⟨[3153, 77149], [3153, 77149], .contexts []⟩,
    ⟨[79209, 3], [79209, 3], .contexts []⟩,
    ⟨[79209, 3], [3153, 77149], .contexts [
        ⟨11726, false, false, [], []⟩,
        ⟨11723, true, false, [], [3]⟩,
        ⟨107, false, false, [79207], []⟩,
        ⟨109, false, false, [79207], []⟩,
        ⟨11712, false, false, [], [13]⟩,
        ⟨473, false, false, [3153], []⟩,
        ⟨11724, false, false, [], []⟩,
        ⟨11725, false, false, [], []⟩,
        ⟨8495, false, false, [3153], []⟩,
        ⟨11698, true, false, [], [77149]⟩
      ]⟩,
    ⟨[77149, 3], [3155, 79209], .contexts [
        ⟨11727, true, false, [3152], [3]⟩,
        ⟨35, false, false, [3152, 79209], []⟩,
        ⟨11700, true, false, [], [79209]⟩
      ]⟩,
    ⟨[1777, 79209], [1777, 79209], .contexts []⟩,
    ⟨[1777, 79209], [1777, 79209], .contexts []⟩,
    ⟨[79209, 5], [79209, 5], .contexts []⟩,
    ⟨[79209], [79209], .contexts []⟩,
    ⟨[79207, 9], [3161, 79207], .contexts [
        ⟨11715, false, false, [], []⟩,
        ⟨11714, false, false, [3158], [79207, 9]⟩,
        ⟨11701, true, false, [3158, 3157], [9]⟩,
        ⟨11713, false, false, [3158], [77147, 3, 9]⟩,
        ⟨8490, true, false, [3158, 3153], [3, 9]⟩,
        ⟨11712, true, false, [3158], [9, 3, 9]⟩,
        ⟨2706, false, false, [3158, 79207], []⟩,
        ⟨11706, false, false, [3158], []⟩,
        ⟨11717, true, false, [], [79207]⟩,
        ⟨11717, true, false, [], [79207]⟩,
        ⟨11716, true, false, [], [79207]⟩
      ]⟩,
    ⟨[3161, 79207], [3161, 79207], .contexts []⟩,
    ⟨[3161, 79207], [3161, 79207], .contexts []⟩,
    ⟨[3161, 79209], [3161, 79209], .contexts []⟩,
    ⟨[3161, 79209], [3161, 79209], .contexts []⟩,
    ⟨[79209, 9], [79209, 9], .contexts []⟩,
    ⟨[3161], [3161], .contexts [
        ⟨24, false, false, [], [3161]⟩
      ]⟩,
    ⟨[79211], [79209, 15], .source 39670⟩,
    ⟨[79209, 15], [79211], .contexts [
        ⟨11740, true, false, [], []⟩
      ]⟩,
    ⟨[79211, 15], [79209], .contexts [
        ⟨11741, true, false, [], [15]⟩,
        ⟨3, false, false, [79209], []⟩,
        ⟨11722, false, false, [], []⟩
      ]⟩,
    ⟨[79211], [79211], .contexts []⟩,
    ⟨[79211], [79211], .contexts []⟩,
    ⟨[79209, 15], [79211], .contexts [
        ⟨11741, false, false, [], []⟩,
        ⟨11743, false, false, [], []⟩,
        ⟨11744, false, false, [], []⟩,
        ⟨11744, false, false, [], []⟩
      ]⟩,
    ⟨[3153, 77151], [3153, 77151], .contexts []⟩,
    ⟨[3153, 77151], [3153, 77151], .contexts []⟩,
    ⟨[79211, 3], [79211, 3], .contexts []⟩,
    ⟨[79211, 3], [3153, 77151], .contexts [
        ⟨11748, false, false, [], []⟩,
        ⟨11745, true, false, [], [3]⟩,
        ⟨34, false, false, [79209], []⟩,
        ⟨37, false, false, [79209], []⟩,
        ⟨11726, false, false, [], [15]⟩,
        ⟨11727, false, false, [], [15]⟩,
        ⟨11724, false, false, [], [15]⟩,
        ⟨11725, false, false, [], [15]⟩,
        ⟨11725, false, false, [], [15]⟩,
        ⟨476, false, false, [3153], []⟩,
        ⟨11746, false, false, [], []⟩,
        ⟨11747, false, false, [], []⟩,
        ⟨8499, false, false, [3153], []⟩,
        ⟨11698, true, false, [], [77151]⟩
      ]⟩,
    ⟨[1777, 79211], [1777, 79211], .contexts []⟩,
    ⟨[79209, 5, 15], [1777, 79211], .contexts [
        ⟨11731, false, false, [], [15]⟩,
        ⟨11731, false, false, [], [15]⟩,
        ⟨11723, true, false, [], [5, 15]⟩,
        ⟨116, false, false, [79207], [15]⟩,
        ⟨117, false, false, [79207], [15]⟩,
        ⟨11704, false, false, [], [13, 15]⟩,
        ⟨11707, false, false, [], [13, 15]⟩,
        ⟨11702, false, false, [], [13, 15]⟩,
        ⟨11703, false, false, [], [13, 15]⟩,
        ⟨11703, false, false, [], [13, 15]⟩,
        ⟨11719, false, false, [1777], [15]⟩,
        ⟨11729, false, false, [], [15]⟩,
        ⟨11730, false, false, [], [15]⟩,
        ⟨11732, false, false, [1777], [15]⟩,
        ⟨11684, true, false, [], [79209, 15]⟩,
        ⟨11729, false, false, [], [15]⟩,
        ⟨11730, false, false, [], [15]⟩,
        ⟨11730, false, false, [], [15]⟩,
        ⟨11741, false, false, [1777], []⟩,
        ⟨11750, false, false, [], []⟩
      ]⟩,
    ⟨[1777, 79211], [1777, 79211], .contexts []⟩,
    ⟨[79211, 5], [79211, 5], .contexts []⟩,
    ⟨[79211], [79211], .contexts []⟩,
    ⟨[79211, 5], [1777, 79211], .contexts [
        ⟨11753, false, false, [], []⟩,
        ⟨11745, true, false, [], [5]⟩,
        ⟨48, false, false, [79209], []⟩,
        ⟨51, false, false, [79209], []⟩,
        ⟨11751, false, false, [], []⟩,
        ⟨11752, false, false, [], []⟩,
        ⟨11754, false, false, [1777], []⟩,
        ⟨11684, true, false, [], [79211]⟩
      ]⟩,
    ⟨[3161, 79211], [3161, 79211], .contexts []⟩,
    ⟨[3161, 79211], [3161, 79211], .contexts []⟩,
    ⟨[3161, 79211], [3161, 79211], .contexts []⟩,
    ⟨[79209, 9, 15], [3161, 79211], .contexts [
        ⟨11738, false, false, [], [15]⟩,
        ⟨11738, false, false, [], [15]⟩,
        ⟨11723, true, false, [], [9, 15]⟩,
        ⟨130, false, false, [79207], [15]⟩,
        ⟨131, false, false, [79207], [15]⟩,
        ⟨11715, false, false, [], [13, 15]⟩,
        ⟨11733, false, false, [], [13, 15]⟩,
        ⟨11734, false, false, [], [13, 15]⟩,
        ⟨11735, false, false, [], [13, 15]⟩,
        ⟨11735, false, false, [], [13, 15]⟩,
        ⟨11719, false, false, [3161], [15]⟩,
        ⟨11736, false, false, [], [15]⟩,
        ⟨11737, false, false, [], [15]⟩,
        ⟨11732, false, false, [3161], [15]⟩,
        ⟨11739, true, false, [], [79209, 15]⟩,
        ⟨11736, false, false, [], [15]⟩,
        ⟨11737, false, false, [], [15]⟩,
        ⟨11737, false, false, [], [15]⟩,
        ⟨11741, false, false, [3161], []⟩,
        ⟨11756, false, false, [], []⟩,
        ⟨11757, false, false, [], []⟩,
        ⟨11758, false, false, [], []⟩
      ]⟩,
    ⟨[79211, 3], [3153, 77151], .contexts [
        ⟨11749, false, false, [], []⟩
      ]⟩,
    ⟨[79213], [79211, 1], .source 39671⟩,
    ⟨[79211, 1], [79213], .contexts [
        ⟨11761, true, false, [], []⟩
      ]⟩,
    ⟨[79213, 1], [79211], .contexts [
        ⟨11762, true, false, [], [1]⟩,
        ⟨18, false, false, [79211], []⟩,
        ⟨11744, false, false, [], []⟩
      ]⟩,
    ⟨[79213], [79213], .contexts []⟩,
    ⟨[79213], [79213], .contexts []⟩,
    ⟨[79215], [79213, 3], .source 39672⟩,
    ⟨[79213, 3], [79215], .contexts [
        ⟨11766, true, false, [], []⟩
      ]⟩,
    ⟨[79215, 3], [79213], .contexts [
        ⟨11767, true, false, [], [3]⟩,
        ⟨35, false, false, [79213], []⟩,
        ⟨11765, false, false, [], []⟩
      ]⟩,
    ⟨[79215], [79215], .contexts []⟩,
    ⟨[79215], [79215], .contexts []⟩,
    ⟨[79213, 1], [79211], .contexts [
        ⟨11763, false, false, [], []⟩,
        ⟨11743, false, false, [], []⟩,
        ⟨11744, false, false, [], []⟩,
        ⟨11744, false, false, [], []⟩
      ]⟩,
    ⟨[3153, 77155], [3153, 77155], .contexts []⟩,
    ⟨[3153, 77155], [3153, 77155], .contexts []⟩,
    ⟨[79215, 1], [79215, 1], .contexts []⟩,
    ⟨[79215, 1], [3153, 77155], .contexts [
        ⟨11774, false, false, [], []⟩,
        ⟨11770, true, false, [], [1]⟩,
        ⟨11770, true, false, [], [1]⟩,
        ⟨11769, true, false, [], [1]⟩,
        ⟨11767, true, false, [], [1]⟩,
        ⟨213, false, false, [79213], []⟩,
        ⟨216, false, false, [79213], []⟩,
        ⟨11771, false, false, [], [3, 1, 3]⟩,
        ⟨11760, false, false, [], [1, 3]⟩,
        ⟨11746, false, false, [], [1, 3]⟩,
        ⟨11747, false, false, [], [1, 3]⟩,
        ⟨11747, false, false, [], [1, 3]⟩,
        ⟨479, false, false, [3153], [3]⟩,
        ⟨483, false, false, [3153], []⟩,
        ⟨11772, false, false, [], []⟩,
        ⟨11773, false, false, [], []⟩,
        ⟨8550, false, false, [3153], []⟩,
        ⟨11698, true, false, [], [77155]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 184. -/
def y322TCContextRaw184 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77155, 1], [3155, 79215], .contexts [
        ⟨11775, true, false, [3152], [1]⟩,
        ⟨18, false, false, [3152, 79215], []⟩,
        ⟨11700, true, false, [], [79215]⟩
      ]⟩,
    ⟨[79215, 1], [3153, 77155], .contexts [
        ⟨11775, false, false, [], []⟩
      ]⟩,
    ⟨[79215, 1], [3153, 77155], .contexts [
        ⟨11774, false, false, [], []⟩,
        ⟨11777, false, false, [], []⟩,
        ⟨11772, false, false, [], []⟩,
        ⟨11773, false, false, [], []⟩,
        ⟨11773, false, false, [], []⟩
      ]⟩,
    ⟨[3153, 77159], [3153, 77159], .contexts []⟩,
    ⟨[3153, 77159], [3153, 77159], .contexts []⟩,
    ⟨[77159, 5], [77159, 5], .contexts []⟩,
    ⟨[79215], [79215], .contexts []⟩,
    ⟨[3152], [3152], .contexts []⟩,
    ⟨[77159, 5], [3155, 79215], .contexts [
        ⟨11781, false, false, [], []⟩,
        ⟨11780, true, false, [3152], [5]⟩,
        ⟨11779, true, false, [3152], [5]⟩,
        ⟨489, true, false, [], [5]⟩,
        ⟨486, true, false, [], [1, 5]⟩,
        ⟨11778, true, false, [3152], [5, 1, 5]⟩,
        ⟨1909, false, false, [3152, 79215], []⟩,
        ⟨11782, false, false, [3152], []⟩,
        ⟨11783, true, false, [], [79215]⟩,
        ⟨11783, true, false, [], [79215]⟩,
        ⟨11700, true, false, [], [79215]⟩
      ]⟩,
    ⟨[3153], [3154], .contexts [
        ⟨11700, true, true, [], []⟩
      ]⟩,
    ⟨[79215, 5], [3153, 77159], .contexts [
        ⟨11784, true, false, [3154], [5]⟩,
        ⟨49, false, false, [3154, 77159], []⟩,
        ⟨11785, true, false, [], [77159]⟩
      ]⟩,
    ⟨[79217], [77157, 9], .source 39673⟩,
    ⟨[77157, 9], [79217], .contexts [
        ⟨11787, true, false, [], []⟩
      ]⟩,
    ⟨[79217, 9], [77157], .contexts [
        ⟨11788, true, false, [], [9]⟩,
        ⟨76, false, false, [77157], []⟩,
        ⟨490, false, false, [], []⟩
      ]⟩,
    ⟨[77157, 9], [79217], .contexts [
        ⟨11788, false, false, [], []⟩
      ]⟩,
    ⟨[79217], [79217], .contexts []⟩,
    ⟨[79217], [79217], .contexts []⟩,
    ⟨[77157, 9], [79217], .contexts [
        ⟨11790, false, false, [], []⟩,
        ⟨11791, false, false, [], []⟩,
        ⟨11792, false, false, [], []⟩,
        ⟨11792, false, false, [], []⟩
      ]⟩,
    ⟨[79217, 3], [79217, 3], .contexts []⟩,
    ⟨[79045], [79045], .contexts [
        ⟨10626, false, false, [], []⟩
      ]⟩,
    ⟨[79045], [79045], .contexts [
        ⟨1118, true, false, [], [79045]⟩
      ]⟩,
    ⟨[79217, 3], [79045], .contexts [
        ⟨11794, false, false, [], []⟩,
        ⟨11793, true, false, [], [3]⟩,
        ⟨306, false, false, [77157], []⟩,
        ⟨307, false, false, [77157], []⟩,
        ⟨10589, true, false, [], [3, 9]⟩,
        ⟨35, false, false, [79043], [9]⟩,
        ⟨10577, false, false, [], [9]⟩,
        ⟨10576, false, false, [], [9]⟩,
        ⟨10577, false, false, [], [9]⟩,
        ⟨10577, false, false, [], [9]⟩,
        ⟨10618, false, false, [], []⟩,
        ⟨10619, false, false, [], []⟩,
        ⟨10620, false, false, [], []⟩,
        ⟨10620, false, false, [], []⟩,
        ⟨11795, false, false, [], []⟩,
        ⟨11796, false, false, [], []⟩
      ]⟩,
    ⟨[77157, 13], [2019, 77157], .contexts [
        ⟨8561, false, false, [], []⟩
      ]⟩,
    ⟨[2019, 77157], [2019, 77157], .contexts []⟩,
    ⟨[2019, 77157], [2019, 77157], .contexts []⟩,
    ⟨[77157, 13], [2019, 77157], .contexts [
        ⟨8558, false, false, [], []⟩,
        ⟨11798, false, false, [], []⟩,
        ⟨11799, false, false, [], []⟩,
        ⟨11800, false, false, [], []⟩,
        ⟨11800, false, false, [], []⟩
      ]⟩,
    ⟨[2019, 79217], [2019, 79217], .contexts []⟩,
    ⟨[2019, 79217], [2019, 79217], .contexts []⟩,
    ⟨[2019, 79217], [2019, 79217], .contexts []⟩,
    ⟨[79217, 13], [79217, 13], .contexts []⟩,
    ⟨[79217], [79217], .contexts []⟩,
    ⟨[2019], [2019], .contexts [
        ⟨24, false, false, [], [2019]⟩
      ]⟩,
    ⟨[79219], [79217, 11], .source 39674⟩,
    ⟨[79217, 11], [79219], .contexts [
        ⟨11808, true, false, [], []⟩
      ]⟩,
    ⟨[79217, 11], [79219], .contexts [
        ⟨11809, false, false, [], []⟩
      ]⟩,
    ⟨[79217, 11], [79219], .contexts [
        ⟨11810, false, false, [], []⟩
      ]⟩,
    ⟨[79219], [79219], .contexts []⟩,
    ⟨[79219], [79219], .contexts []⟩,
    ⟨[79217, 11], [79219], .contexts [
        ⟨11811, false, false, [], []⟩,
        ⟨11812, false, false, [], []⟩,
        ⟨11813, false, false, [], []⟩,
        ⟨11813, false, false, [], []⟩
      ]⟩,
    ⟨[79217, 3], [79045], .contexts [
        ⟨11797, false, false, [], []⟩
      ]⟩,
    ⟨[2019, 79219], [2019, 79219], .contexts []⟩,
    ⟨[2019, 79219], [2019, 79219], .contexts []⟩,
    ⟨[2019, 79219], [2019, 79219], .contexts []⟩,
    ⟨[79219, 13], [2019, 79219], .contexts [
        ⟨11814, true, false, [], [13]⟩,
        ⟨352, false, false, [79217], []⟩,
        ⟨353, false, false, [79217], []⟩,
        ⟨11805, false, false, [], [11]⟩,
        ⟨11805, false, false, [], [11]⟩,
        ⟨11793, true, false, [], [13, 11]⟩,
        ⟨315, false, false, [77157], [11]⟩,
        ⟨316, false, false, [77157], [11]⟩,
        ⟨11801, false, false, [], [9, 11]⟩,
        ⟨11788, false, false, [2019], [11]⟩,
        ⟨11802, false, false, [], [11]⟩,
        ⟨11803, false, false, [], [11]⟩,
        ⟨11804, false, false, [], [11]⟩,
        ⟨11806, false, false, [2019], [11]⟩,
        ⟨11807, true, false, [], [79217, 11]⟩,
        ⟨11802, false, false, [], [11]⟩,
        ⟨11804, false, false, [], [11]⟩,
        ⟨11804, false, false, [], [11]⟩,
        ⟨11809, false, false, [2019], []⟩,
        ⟨11816, false, false, [], []⟩,
        ⟨11817, false, false, [], []⟩,
        ⟨11818, false, false, [], []⟩
      ]⟩,
    ⟨[79221], [79219, 1], .source 39675⟩,
    ⟨[79219, 1], [79221], .contexts [
        ⟨11820, true, false, [], []⟩
      ]⟩,
    ⟨[79221, 1], [79219], .contexts [
        ⟨11821, true, false, [], [1]⟩,
        ⟨18, false, false, [79219], []⟩,
        ⟨11813, false, false, [], []⟩
      ]⟩,
    ⟨[79223], [79221, 13], .source 39676⟩,
    ⟨[79221, 13], [79223], .contexts [
        ⟨11823, true, false, [], []⟩
      ]⟩,
    ⟨[79223], [79223], .contexts []⟩,
    ⟨[2019, 79221], [2019, 79221], .contexts []⟩,
    ⟨[2019, 79221], [2019, 79221], .contexts []⟩,
    ⟨[2019, 79221], [2019, 79221], .contexts []⟩,
    ⟨[2019, 79223], [2019, 79223], .contexts []⟩,
    ⟨[2019, 79223], [2019, 79223], .contexts []⟩,
    ⟨[2019, 79223], [2019, 79223], .contexts []⟩,
    ⟨[79223, 1], [79223, 1], .contexts []⟩,
    ⟨[79223], [79223], .contexts []⟩,
    ⟨[79223, 1], [2019, 79223], .contexts [
        ⟨11832, false, false, [], []⟩,
        ⟨11825, true, false, [], [1]⟩,
        ⟨11825, true, false, [], [1]⟩,
        ⟨11824, true, false, [], [1]⟩,
        ⟨387, false, false, [79221], []⟩,
        ⟨390, false, false, [79221], []⟩,
        ⟨11822, false, false, [], [13, 1, 13]⟩,
        ⟨11812, false, false, [], [13, 1, 13]⟩,
        ⟨11813, false, false, [], [13, 1, 13]⟩,
        ⟨11813, false, false, [], [13, 1, 13]⟩,
        ⟨11819, false, false, [], [1, 13]⟩,
        ⟨11807, true, false, [], [79219, 1, 13]⟩,
        ⟨11816, false, false, [], [1, 13]⟩,
        ⟨11818, false, false, [], [1, 13]⟩,
        ⟨11818, false, false, [], [1, 13]⟩,
        ⟨11821, false, false, [2019], [13]⟩,
        ⟨11826, false, false, [], [13]⟩,
        ⟨11827, false, false, [], [13]⟩,
        ⟨11828, false, false, [], [13]⟩,
        ⟨11824, false, false, [2019], []⟩,
        ⟨11829, false, false, [], []⟩,
        ⟨11830, false, false, [], []⟩,
        ⟨11831, false, false, [], []⟩,
        ⟨11833, false, false, [2019], []⟩
      ]⟩,
    ⟨[79223, 1], [2019, 79223], .contexts [
        ⟨11834, false, false, [], []⟩,
        ⟨11807, true, false, [], [79223]⟩
      ]⟩,
    ⟨[79225], [79223, 15], .source 39677⟩,
    ⟨[79223, 15], [79225], .contexts [
        ⟨11836, true, false, [], []⟩
      ]⟩,
    ⟨[79225], [79225], .contexts []⟩,
    ⟨[79225], [79225], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 185. -/
def y322TCContextRaw185 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2019, 79225], [2019, 79225], .contexts []⟩,
    ⟨[2019, 79225], [2019, 79225], .contexts []⟩,
    ⟨[79225], [79225], .contexts []⟩,
    ⟨[79227], [79225, 3], .source 39678⟩,
    ⟨[79225, 3], [79227], .contexts [
        ⟨11843, true, false, [], []⟩
      ]⟩,
    ⟨[79229], [79227, 5], .source 39679⟩,
    ⟨[79227], [79227], .contexts []⟩,
    ⟨[79231], [79229, 1], .source 39680⟩,
    ⟨[79229], [79229], .contexts []⟩,
    ⟨[79233], [79231, 9], .source 39681⟩,
    ⟨[79231], [79231], .contexts []⟩,
    ⟨[79235], [79233, 11], .source 39682⟩,
    ⟨[79233], [79233], .contexts []⟩,
    ⟨[79237], [79235, 1], .source 39683⟩,
    ⟨[79235], [79235], .contexts []⟩,
    ⟨[79239], [79237, 13], .source 39684⟩,
    ⟨[79237], [79237], .contexts []⟩,
    ⟨[79241], [79239, 15], .source 39685⟩,
    ⟨[79239], [79239], .contexts []⟩,
    ⟨[79243], [79241, 1], .source 39686⟩,
    ⟨[79241], [79241], .contexts []⟩,
    ⟨[79245], [79243, 3], .source 39687⟩,
    ⟨[79243], [79243], .contexts []⟩,
    ⟨[79247], [79245, 5], .source 39688⟩,
    ⟨[79245], [79245], .contexts []⟩,
    ⟨[79249], [79247, 1], .source 39689⟩,
    ⟨[79247], [79247], .contexts []⟩,
    ⟨[79251], [79249, 9], .source 39690⟩,
    ⟨[79249], [79249], .contexts []⟩,
    ⟨[79253], [79251, 11], .source 39691⟩,
    ⟨[79251], [79251], .contexts []⟩,
    ⟨[79255], [79253, 1], .source 39692⟩,
    ⟨[79253], [79253], .contexts []⟩,
    ⟨[79257], [79255, 13], .source 39693⟩,
    ⟨[79255], [79255], .contexts []⟩,
    ⟨[79259], [79257, 15], .source 39694⟩,
    ⟨[79257], [79257], .contexts []⟩,
    ⟨[79261], [79259, 1], .source 39695⟩,
    ⟨[79259], [79259], .contexts []⟩,
    ⟨[79263], [79261, 3], .source 39696⟩,
    ⟨[79261], [79261], .contexts []⟩,
    ⟨[79265], [79263, 5], .source 39697⟩,
    ⟨[79263], [79263], .contexts []⟩,
    ⟨[79267], [79265, 1], .source 39698⟩,
    ⟨[79265], [79265], .contexts []⟩,
    ⟨[79269], [79267, 9], .source 39699⟩,
    ⟨[79267], [79267], .contexts []⟩,
    ⟨[79271], [79269, 11], .source 39700⟩,
    ⟨[79269], [79269], .contexts []⟩,
    ⟨[79273], [79271, 1], .source 39701⟩,
    ⟨[79271], [79271], .contexts []⟩,
    ⟨[79275], [79273, 13], .source 39702⟩,
    ⟨[79273], [79273], .contexts []⟩,
    ⟨[79277], [79275, 15], .source 39703⟩,
    ⟨[79275], [79275], .contexts []⟩,
    ⟨[79279], [79277, 1], .source 39704⟩,
    ⟨[79277], [79277], .contexts []⟩,
    ⟨[79281], [79279, 3], .source 39705⟩,
    ⟨[79279], [79279], .contexts []⟩,
    ⟨[79283], [79281, 5], .source 39706⟩,
    ⟨[79281], [79281], .contexts []⟩,
    ⟨[79285], [79283, 1], .source 39707⟩,
    ⟨[79283], [79283], .contexts []⟩,
    ⟨[79287], [79285, 9], .source 39708⟩]

/-- Exact literal claimed equations and contextual derivations, block 186. -/
def y322TCContextRaw186 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79285], [79285], .contexts []⟩,
    ⟨[79289], [79287, 11], .source 39709⟩,
    ⟨[79287], [79287], .contexts []⟩,
    ⟨[79291], [79289, 1], .source 39710⟩,
    ⟨[79289], [79289], .contexts []⟩,
    ⟨[79293], [79291, 13], .source 39711⟩,
    ⟨[79291], [79291], .contexts []⟩,
    ⟨[79295], [79293, 15], .source 39712⟩,
    ⟨[79293], [79293], .contexts []⟩,
    ⟨[79297], [79295, 1], .source 39713⟩,
    ⟨[79295], [79295], .contexts []⟩,
    ⟨[79299], [79297, 3], .source 39714⟩,
    ⟨[79297], [79297], .contexts []⟩,
    ⟨[79301], [79299, 5], .source 39715⟩,
    ⟨[79299], [79299], .contexts []⟩,
    ⟨[79303], [79301, 1], .source 39716⟩,
    ⟨[79301], [79301], .contexts []⟩,
    ⟨[79305], [79303, 9], .source 39717⟩,
    ⟨[79303], [79303], .contexts []⟩,
    ⟨[79307], [79305, 11], .source 39718⟩,
    ⟨[79305], [79305], .contexts []⟩,
    ⟨[79309], [79307, 1], .source 39719⟩,
    ⟨[79307], [79307], .contexts []⟩,
    ⟨[79311], [79309, 13], .source 39720⟩,
    ⟨[79309], [79309], .contexts []⟩,
    ⟨[79313], [79311, 15], .source 39721⟩,
    ⟨[79311], [79311], .contexts []⟩,
    ⟨[79315], [79313, 1], .source 39722⟩,
    ⟨[79313], [79313], .contexts []⟩,
    ⟨[79317], [79315, 3], .source 39723⟩,
    ⟨[79315], [79315], .contexts []⟩,
    ⟨[79319], [79317, 5], .source 39724⟩,
    ⟨[79317], [79317], .contexts []⟩,
    ⟨[79319, 5], [79317], .contexts [
        ⟨11935, false, false, [], [5]⟩,
        ⟨49, false, false, [79317], []⟩,
        ⟨11936, false, false, [], []⟩
      ]⟩,
    ⟨[79321], [79319, 1], .source 39725⟩,
    ⟨[79319], [79319], .contexts []⟩,
    ⟨[79321, 1], [79319], .contexts [
        ⟨11938, false, false, [], [1]⟩,
        ⟨18, false, false, [79319], []⟩,
        ⟨11939, false, false, [], []⟩
      ]⟩,
    ⟨[79323], [79321, 9], .source 39726⟩,
    ⟨[79321], [79321], .contexts []⟩,
    ⟨[79323, 9], [79321], .contexts [
        ⟨11941, false, false, [], [9]⟩,
        ⟨76, false, false, [79321], []⟩,
        ⟨11942, false, false, [], []⟩
      ]⟩,
    ⟨[79325], [79323, 11], .source 39727⟩,
    ⟨[79323], [79323], .contexts []⟩,
    ⟨[79325, 11], [79323], .contexts [
        ⟨11944, false, false, [], [11]⟩,
        ⟨90, false, false, [79323], []⟩,
        ⟨11945, false, false, [], []⟩
      ]⟩,
    ⟨[79327], [79325, 1], .source 39728⟩,
    ⟨[79325], [79325], .contexts []⟩,
    ⟨[79327, 1], [79325], .contexts [
        ⟨11947, false, false, [], [1]⟩,
        ⟨18, false, false, [79325], []⟩,
        ⟨11948, false, false, [], []⟩
      ]⟩,
    ⟨[79329], [79327, 13], .source 39729⟩,
    ⟨[79327], [79327], .contexts []⟩,
    ⟨[79329, 13], [79327], .contexts [
        ⟨11950, false, false, [], [13]⟩,
        ⟨98, false, false, [79327], []⟩,
        ⟨11951, false, false, [], []⟩
      ]⟩,
    ⟨[79331], [79329, 15], .source 39730⟩,
    ⟨[79329], [79329], .contexts []⟩,
    ⟨[79331, 15], [79329], .contexts [
        ⟨11953, false, false, [], [15]⟩,
        ⟨3, false, false, [79329], []⟩,
        ⟨11954, false, false, [], []⟩
      ]⟩,
    ⟨[79333], [79331, 1], .source 39731⟩,
    ⟨[79331], [79331], .contexts []⟩,
    ⟨[79333, 1], [79331], .contexts [
        ⟨11956, false, false, [], [1]⟩,
        ⟨18, false, false, [79331], []⟩,
        ⟨11957, false, false, [], []⟩
      ]⟩,
    ⟨[79335], [79333, 3], .source 39732⟩,
    ⟨[79333, 3], [79335], .contexts [
        ⟨11959, true, false, [], []⟩
      ]⟩,
    ⟨[79333], [79333], .contexts []⟩,
    ⟨[79335, 3], [79333], .contexts [
        ⟨11960, true, false, [], [3]⟩,
        ⟨35, false, false, [79333], []⟩,
        ⟨11961, false, false, [], []⟩
      ]⟩,
    ⟨[79337], [79335, 5], .source 39733⟩,
    ⟨[79335], [79335], .contexts []⟩,
    ⟨[79337, 5], [79335], .contexts [
        ⟨11963, false, false, [], [5]⟩,
        ⟨49, false, false, [79335], []⟩,
        ⟨11964, false, false, [], []⟩
      ]⟩,
    ⟨[79339], [79337, 1], .source 39734⟩,
    ⟨[79337], [79337], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 187. -/
def y322TCContextRaw187 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79339, 1], [79337], .contexts [
        ⟨11966, false, false, [], [1]⟩,
        ⟨18, false, false, [79337], []⟩,
        ⟨11967, false, false, [], []⟩
      ]⟩,
    ⟨[79341], [79339, 9], .source 39735⟩,
    ⟨[79339], [79339], .contexts []⟩,
    ⟨[79341, 9], [79339], .contexts [
        ⟨11969, false, false, [], [9]⟩,
        ⟨76, false, false, [79339], []⟩,
        ⟨11970, false, false, [], []⟩
      ]⟩,
    ⟨[79343], [79341, 11], .source 39736⟩,
    ⟨[79341], [79341], .contexts []⟩,
    ⟨[79345], [79343, 1], .source 39737⟩,
    ⟨[79343], [79343], .contexts []⟩,
    ⟨[79345, 1], [79343], .contexts [
        ⟨11974, false, false, [], [1]⟩,
        ⟨18, false, false, [79343], []⟩,
        ⟨11975, false, false, [], []⟩
      ]⟩,
    ⟨[79347], [79345, 13], .source 39738⟩,
    ⟨[79345], [79345], .contexts []⟩,
    ⟨[79347, 13], [79345], .contexts [
        ⟨11977, false, false, [], [13]⟩,
        ⟨98, false, false, [79345], []⟩,
        ⟨11978, false, false, [], []⟩
      ]⟩,
    ⟨[79349], [79347, 15], .source 39739⟩,
    ⟨[79347], [79347], .contexts []⟩,
    ⟨[79349, 15], [79347], .contexts [
        ⟨11980, false, false, [], [15]⟩,
        ⟨3, false, false, [79347], []⟩,
        ⟨11981, false, false, [], []⟩
      ]⟩,
    ⟨[79351], [79349, 1], .source 39740⟩,
    ⟨[79349], [79349], .contexts []⟩,
    ⟨[79351, 1], [79349], .contexts [
        ⟨11983, false, false, [], [1]⟩,
        ⟨18, false, false, [79349], []⟩,
        ⟨11984, false, false, [], []⟩
      ]⟩,
    ⟨[79353], [79351, 3], .source 39741⟩,
    ⟨[79351, 3], [79353], .contexts [
        ⟨11986, true, false, [], []⟩
      ]⟩,
    ⟨[79351], [79351], .contexts []⟩,
    ⟨[79353, 3], [79351], .contexts [
        ⟨11987, true, false, [], [3]⟩,
        ⟨35, false, false, [79351], []⟩,
        ⟨11988, false, false, [], []⟩
      ]⟩,
    ⟨[79353], [79353], .contexts []⟩,
    ⟨[79353], [79353], .contexts []⟩,
    ⟨[79349, 15], [79347], .contexts [
        ⟨11982, false, false, [], []⟩
      ]⟩,
    ⟨[79347], [79347], .contexts []⟩,
    ⟨[79347, 13], [79345], .contexts [
        ⟨11979, false, false, [], []⟩
      ]⟩,
    ⟨[79345], [79345], .contexts []⟩,
    ⟨[79345, 1], [79343], .contexts [
        ⟨11976, false, false, [], []⟩
      ]⟩,
    ⟨[79343], [79343], .contexts []⟩,
    ⟨[79343, 11], [79341], .contexts [
        ⟨11972, false, false, [], [11]⟩,
        ⟨90, false, false, [79341], []⟩,
        ⟨11973, false, false, [], []⟩
      ]⟩,
    ⟨[79341], [79341], .contexts []⟩,
    ⟨[79351, 1, 15, 13, 1, 11], [79341], .contexts [
        ⟨11985, false, false, [], [15, 13, 1, 11]⟩,
        ⟨11984, false, false, [], [15, 13, 1, 11]⟩,
        ⟨11984, false, false, [], [15, 13, 1, 11]⟩,
        ⟨11992, false, false, [], [13, 1, 11]⟩,
        ⟨11993, false, false, [], [13, 1, 11]⟩,
        ⟨11981, false, false, [], [13, 1, 11]⟩,
        ⟨11981, false, false, [], [13, 1, 11]⟩,
        ⟨11994, false, false, [], [1, 11]⟩,
        ⟨11995, false, false, [], [1, 11]⟩,
        ⟨11978, false, false, [], [1, 11]⟩,
        ⟨11978, false, false, [], [1, 11]⟩,
        ⟨11996, false, false, [], [11]⟩,
        ⟨11997, false, false, [], [11]⟩,
        ⟨11975, false, false, [], [11]⟩,
        ⟨11975, false, false, [], [11]⟩,
        ⟨11998, false, false, [], []⟩,
        ⟨11999, false, false, [], []⟩,
        ⟨11973, false, false, [], []⟩,
        ⟨11973, false, false, [], []⟩
      ]⟩,
    ⟨[79339], [79339], .contexts []⟩,
    ⟨[79337], [79337], .contexts []⟩,
    ⟨[79335], [79335], .contexts []⟩,
    ⟨[79333], [79333], .contexts []⟩,
    ⟨[79333, 1], [79331], .contexts [
        ⟨11958, false, false, [], []⟩
      ]⟩,
    ⟨[79331], [79331], .contexts []⟩,
    ⟨[79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1], [79331], .contexts [
        ⟨12000, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨11971, false, false, [], [1, 5, 3, 1]⟩,
        ⟨12001, false, false, [], [1, 5, 3, 1]⟩,
        ⟨11970, false, false, [], [1, 5, 3, 1]⟩,
        ⟨11970, false, false, [], [1, 5, 3, 1]⟩,
        ⟨11968, false, false, [], [5, 3, 1]⟩,
        ⟨12002, false, false, [], [5, 3, 1]⟩,
        ⟨11967, false, false, [], [5, 3, 1]⟩,
        ⟨11967, false, false, [], [5, 3, 1]⟩,
        ⟨11965, false, false, [], [3, 1]⟩,
        ⟨12003, false, false, [], [3, 1]⟩,
        ⟨11964, false, false, [], [3, 1]⟩,
        ⟨11964, false, false, [], [3, 1]⟩,
        ⟨11962, false, false, [], [1]⟩,
        ⟨12004, false, false, [], [1]⟩,
        ⟨11961, false, false, [], [1]⟩,
        ⟨11961, false, false, [], [1]⟩,
        ⟨12005, false, false, [], []⟩,
        ⟨12006, false, false, [], []⟩,
        ⟨11957, false, false, [], []⟩,
        ⟨11957, false, false, [], []⟩
      ]⟩,
    ⟨[79325], [79325], .contexts []⟩,
    ⟨[79323], [79323], .contexts []⟩,
    ⟨[79321], [79321], .contexts []⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9
    ], [79321], .contexts [
        ⟨12007, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨11955, false, false, [], [13, 1, 11, 9]⟩,
        ⟨11954, false, false, [], [13, 1, 11, 9]⟩,
        ⟨11954, false, false, [], [13, 1, 11, 9]⟩,
        ⟨11952, false, false, [], [1, 11, 9]⟩,
        ⟨11951, false, false, [], [1, 11, 9]⟩,
        ⟨11951, false, false, [], [1, 11, 9]⟩,
        ⟨11949, false, false, [], [11, 9]⟩,
        ⟨12008, false, false, [], [11, 9]⟩,
        ⟨11948, false, false, [], [11, 9]⟩,
        ⟨11948, false, false, [], [11, 9]⟩,
        ⟨11946, false, false, [], [9]⟩,
        ⟨12009, false, false, [], [9]⟩,
        ⟨11945, false, false, [], [9]⟩,
        ⟨11945, false, false, [], [9]⟩,
        ⟨11943, false, false, [], []⟩,
        ⟨12010, false, false, [], []⟩,
        ⟨11942, false, false, [], []⟩,
        ⟨11942, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [79311], .contexts [
        ⟨12011, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨11940, false, false, [], [5, 3, 1, 15]⟩,
        ⟨11939, false, false, [], [5, 3, 1, 15]⟩,
        ⟨11939, false, false, [], [5, 3, 1, 15]⟩,
        ⟨11937, false, false, [], [3, 1, 15]⟩,
        ⟨11936, false, false, [], [3, 1, 15]⟩,
        ⟨11936, false, false, [], [3, 1, 15]⟩,
        ⟨11933, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [79315], [1, 15]⟩,
        ⟨11934, false, false, [], [1, 15]⟩,
        ⟨11934, false, false, [], [1, 15]⟩,
        ⟨11934, false, false, [], [1, 15]⟩,
        ⟨11931, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [79313], [15]⟩,
        ⟨11932, false, false, [], [15]⟩,
        ⟨11932, false, false, [], [15]⟩,
        ⟨11932, false, false, [], [15]⟩,
        ⟨11929, false, false, [], [15]⟩,
        ⟨3, false, false, [79311], []⟩,
        ⟨11930, false, false, [], []⟩,
        ⟨11930, false, false, [], []⟩,
        ⟨11930, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [79303], .contexts [
        ⟨12012, false, false, [], [13, 1, 11, 9]⟩,
        ⟨11927, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [79309], [1, 11, 9]⟩,
        ⟨11928, false, false, [], [1, 11, 9]⟩,
        ⟨11928, false, false, [], [1, 11, 9]⟩,
        ⟨11928, false, false, [], [1, 11, 9]⟩,
        ⟨11925, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [79307], [11, 9]⟩,
        ⟨11926, false, false, [], [11, 9]⟩,
        ⟨11926, false, false, [], [11, 9]⟩,
        ⟨11926, false, false, [], [11, 9]⟩,
        ⟨11923, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [79305], [9]⟩,
        ⟨11924, false, false, [], [9]⟩,
        ⟨11924, false, false, [], [9]⟩,
        ⟨11924, false, false, [], [9]⟩,
        ⟨11921, false, false, [], [9]⟩,
        ⟨76, false, false, [79303], []⟩,
        ⟨11922, false, false, [], []⟩,
        ⟨11922, false, false, [], []⟩,
        ⟨11922, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [79295], .contexts [
        ⟨12013, false, false, [], [1, 5, 3, 1]⟩,
        ⟨11919, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [79301], [5, 3, 1]⟩,
        ⟨11920, false, false, [], [5, 3, 1]⟩,
        ⟨11920, false, false, [], [5, 3, 1]⟩,
        ⟨11920, false, false, [], [5, 3, 1]⟩,
        ⟨11917, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [79299], [3, 1]⟩,
        ⟨11918, false, false, [], [3, 1]⟩,
        ⟨11918, false, false, [], [3, 1]⟩,
        ⟨11918, false, false, [], [3, 1]⟩,
        ⟨11915, false, false, [], [3, 1]⟩,
        ⟨35, false, false, [79297], [1]⟩,
        ⟨11916, false, false, [], [1]⟩,
        ⟨11916, false, false, [], [1]⟩,
        ⟨11916, false, false, [], [1]⟩,
        ⟨11913, false, false, [], [1]⟩,
        ⟨18, false, false, [79295], []⟩,
        ⟨11914, false, false, [], []⟩,
        ⟨11914, false, false, [], []⟩,
        ⟨11914, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [79287], .contexts [
        ⟨12014, false, false, [], [15, 13, 1, 11]⟩,
        ⟨11911, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [79293], [13, 1, 11]⟩,
        ⟨11912, false, false, [], [13, 1, 11]⟩,
        ⟨11912, false, false, [], [13, 1, 11]⟩,
        ⟨11912, false, false, [], [13, 1, 11]⟩,
        ⟨11909, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [79291], [1, 11]⟩,
        ⟨11910, false, false, [], [1, 11]⟩,
        ⟨11910, false, false, [], [1, 11]⟩,
        ⟨11910, false, false, [], [1, 11]⟩,
        ⟨11907, false, false, [], [1, 11]⟩,
        ⟨18, false, false, [79289], [11]⟩,
        ⟨11908, false, false, [], [11]⟩,
        ⟨11908, false, false, [], [11]⟩,
        ⟨11908, false, false, [], [11]⟩,
        ⟨11905, false, false, [], [11]⟩,
        ⟨90, false, false, [79287], []⟩,
        ⟨11906, false, false, [], []⟩,
        ⟨11906, false, false, [], []⟩,
        ⟨11906, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [79279], .contexts [
        ⟨12015, false, false, [], [9, 1, 5, 3]⟩,
        ⟨11903, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [79285], [1, 5, 3]⟩,
        ⟨11904, false, false, [], [1, 5, 3]⟩,
        ⟨11904, false, false, [], [1, 5, 3]⟩,
        ⟨11904, false, false, [], [1, 5, 3]⟩,
        ⟨11901, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [79283], [5, 3]⟩,
        ⟨11902, false, false, [], [5, 3]⟩,
        ⟨11902, false, false, [], [5, 3]⟩,
        ⟨11902, false, false, [], [5, 3]⟩,
        ⟨11899, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [79281], [3]⟩,
        ⟨11900, false, false, [], [3]⟩,
        ⟨11900, false, false, [], [3]⟩,
        ⟨11900, false, false, [], [3]⟩,
        ⟨11897, false, false, [], [3]⟩,
        ⟨35, false, false, [79279], []⟩,
        ⟨11898, false, false, [], []⟩,
        ⟨11898, false, false, [], []⟩,
        ⟨11898, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [79271], .contexts [
        ⟨12016, false, false, [], [1, 15, 13, 1]⟩,
        ⟨11895, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [79277], [15, 13, 1]⟩,
        ⟨11896, false, false, [], [15, 13, 1]⟩,
        ⟨11896, false, false, [], [15, 13, 1]⟩,
        ⟨11896, false, false, [], [15, 13, 1]⟩,
        ⟨11893, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [79275], [13, 1]⟩,
        ⟨11894, false, false, [], [13, 1]⟩,
        ⟨11894, false, false, [], [13, 1]⟩,
        ⟨11894, false, false, [], [13, 1]⟩,
        ⟨11891, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [79273], [1]⟩,
        ⟨11892, false, false, [], [1]⟩,
        ⟨11892, false, false, [], [1]⟩,
        ⟨11892, false, false, [], [1]⟩,
        ⟨11889, false, false, [], [1]⟩,
        ⟨18, false, false, [79271], []⟩,
        ⟨11890, false, false, [], []⟩,
        ⟨11890, false, false, [], []⟩,
        ⟨11890, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [79263], .contexts [
        ⟨12017, false, false, [], [11, 9, 1, 5]⟩,
        ⟨11887, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [79269], [9, 1, 5]⟩,
        ⟨11888, false, false, [], [9, 1, 5]⟩,
        ⟨11888, false, false, [], [9, 1, 5]⟩,
        ⟨11888, false, false, [], [9, 1, 5]⟩,
        ⟨11885, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [79267], [1, 5]⟩,
        ⟨11886, false, false, [], [1, 5]⟩,
        ⟨11886, false, false, [], [1, 5]⟩,
        ⟨11886, false, false, [], [1, 5]⟩,
        ⟨11883, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [79265], [5]⟩,
        ⟨11884, false, false, [], [5]⟩,
        ⟨11884, false, false, [], [5]⟩,
        ⟨11884, false, false, [], [5]⟩,
        ⟨11881, false, false, [], [5]⟩,
        ⟨49, false, false, [79263], []⟩,
        ⟨11882, false, false, [], []⟩,
        ⟨11882, false, false, [], []⟩,
        ⟨11882, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [79255], .contexts [
        ⟨12018, false, false, [], [3, 1, 15, 13]⟩,
        ⟨11879, false, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [79261], [1, 15, 13]⟩,
        ⟨11880, false, false, [], [1, 15, 13]⟩,
        ⟨11880, false, false, [], [1, 15, 13]⟩,
        ⟨11880, false, false, [], [1, 15, 13]⟩,
        ⟨11877, false, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [79259], [15, 13]⟩,
        ⟨11878, false, false, [], [15, 13]⟩,
        ⟨11878, false, false, [], [15, 13]⟩,
        ⟨11878, false, false, [], [15, 13]⟩,
        ⟨11875, false, false, [], [15, 13]⟩,
        ⟨3, false, false, [79257], [13]⟩,
        ⟨11876, false, false, [], [13]⟩,
        ⟨11876, false, false, [], [13]⟩,
        ⟨11876, false, false, [], [13]⟩,
        ⟨11873, false, false, [], [13]⟩,
        ⟨98, false, false, [79255], []⟩,
        ⟨11874, false, false, [], []⟩,
        ⟨11874, false, false, [], []⟩,
        ⟨11874, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [79247], .contexts [
        ⟨12019, false, false, [], [1, 11, 9, 1]⟩,
        ⟨11871, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [79253], [11, 9, 1]⟩,
        ⟨11872, false, false, [], [11, 9, 1]⟩,
        ⟨11872, false, false, [], [11, 9, 1]⟩,
        ⟨11872, false, false, [], [11, 9, 1]⟩,
        ⟨11869, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [79251], [9, 1]⟩,
        ⟨11870, false, false, [], [9, 1]⟩,
        ⟨11870, false, false, [], [9, 1]⟩,
        ⟨11870, false, false, [], [9, 1]⟩,
        ⟨11867, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [79249], [1]⟩,
        ⟨11868, false, false, [], [1]⟩,
        ⟨11868, false, false, [], [1]⟩,
        ⟨11868, false, false, [], [1]⟩,
        ⟨11865, false, false, [], [1]⟩,
        ⟨18, false, false, [79247], []⟩,
        ⟨11866, false, false, [], []⟩,
        ⟨11866, false, false, [], []⟩,
        ⟨11866, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [79239], .contexts [
        ⟨12020, false, false, [], [5, 3, 1, 15]⟩,
        ⟨11863, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [79245], [3, 1, 15]⟩,
        ⟨11864, false, false, [], [3, 1, 15]⟩,
        ⟨11864, false, false, [], [3, 1, 15]⟩,
        ⟨11864, false, false, [], [3, 1, 15]⟩,
        ⟨11861, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [79243], [1, 15]⟩,
        ⟨11862, false, false, [], [1, 15]⟩,
        ⟨11862, false, false, [], [1, 15]⟩,
        ⟨11862, false, false, [], [1, 15]⟩,
        ⟨11859, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [79241], [15]⟩,
        ⟨11860, false, false, [], [15]⟩,
        ⟨11860, false, false, [], [15]⟩,
        ⟨11860, false, false, [], [15]⟩,
        ⟨11857, false, false, [], [15]⟩,
        ⟨3, false, false, [79239], []⟩,
        ⟨11858, false, false, [], []⟩,
        ⟨11858, false, false, [], []⟩,
        ⟨11858, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [79231], .contexts [
        ⟨12021, false, false, [], [13, 1, 11, 9]⟩,
        ⟨11855, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [79237], [1, 11, 9]⟩,
        ⟨11856, false, false, [], [1, 11, 9]⟩,
        ⟨11856, false, false, [], [1, 11, 9]⟩,
        ⟨11856, false, false, [], [1, 11, 9]⟩,
        ⟨11853, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [79235], [11, 9]⟩,
        ⟨11854, false, false, [], [11, 9]⟩,
        ⟨11854, false, false, [], [11, 9]⟩,
        ⟨11854, false, false, [], [11, 9]⟩,
        ⟨11851, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [79233], [9]⟩,
        ⟨11852, false, false, [], [9]⟩,
        ⟨11852, false, false, [], [9]⟩,
        ⟨11852, false, false, [], [9]⟩,
        ⟨11849, false, false, [], [9]⟩,
        ⟨76, false, false, [79231], []⟩,
        ⟨11850, false, false, [], []⟩,
        ⟨11850, false, false, [], []⟩,
        ⟨11850, false, false, [], []⟩
      ]⟩,
    ⟨[79225, 1], [2019, 79225], .contexts [
        ⟨11839, true, false, [], [1]⟩,
        ⟨11839, true, false, [], [1]⟩,
        ⟨11838, true, false, [], [1]⟩,
        ⟨11837, true, false, [], [1]⟩,
        ⟨17, false, false, [79223], []⟩,
        ⟨21, false, false, [79223], []⟩,
        ⟨11832, false, false, [], [15]⟩,
        ⟨11835, false, false, [], [15]⟩,
        ⟨11829, false, false, [], [15]⟩,
        ⟨11831, false, false, [], [15]⟩,
        ⟨11831, false, false, [], [15]⟩,
        ⟨11837, false, false, [2019], []⟩,
        ⟨11840, false, false, [], []⟩,
        ⟨11841, false, false, [], []⟩,
        ⟨11842, false, false, [2019], []⟩,
        ⟨11807, true, false, [], [79225]⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [2019, 79225], .contexts [
        ⟨12022, false, false, [], [1, 5, 3, 1]⟩,
        ⟨11847, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [79229], [5, 3, 1]⟩,
        ⟨11848, false, false, [], [5, 3, 1]⟩,
        ⟨11848, false, false, [], [5, 3, 1]⟩,
        ⟨11848, false, false, [], [5, 3, 1]⟩,
        ⟨11845, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [79227], [3, 1]⟩,
        ⟨11846, false, false, [], [3, 1]⟩,
        ⟨11846, false, false, [], [3, 1]⟩,
        ⟨11846, false, false, [], [3, 1]⟩,
        ⟨11844, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [79225], [1]⟩,
        ⟨11839, false, false, [], [1]⟩,
        ⟨11838, false, false, [], [1]⟩,
        ⟨11839, false, false, [], [1]⟩,
        ⟨11839, false, false, [], [1]⟩,
        ⟨12023, false, false, [], []⟩,
        ⟨11840, false, false, [], []⟩,
        ⟨11841, false, false, [], []⟩,
        ⟨11841, false, false, [], []⟩
      ]⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [2019, 79217], .contexts [
        ⟨12024, false, false, [], [15, 13, 1, 11]⟩,
        ⟨11837, true, false, [2019], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [2019, 79223], [13, 1, 11]⟩,
        ⟨11825, false, false, [2019], [13, 1, 11]⟩,
        ⟨11829, false, false, [], [13, 1, 11]⟩,
        ⟨11830, false, false, [], [13, 1, 11]⟩,
        ⟨11831, false, false, [], [13, 1, 11]⟩,
        ⟨11824, true, false, [2019], [13, 1, 11]⟩,
        ⟨98, false, false, [2019, 79221], [1, 11]⟩,
        ⟨11826, false, false, [], [1, 11]⟩,
        ⟨11827, false, false, [], [1, 11]⟩,
        ⟨11828, false, false, [], [1, 11]⟩,
        ⟨11822, false, false, [2019], [11]⟩,
        ⟨11816, false, false, [], [11]⟩,
        ⟨11817, false, false, [], [11]⟩,
        ⟨11818, false, false, [], [11]⟩,
        ⟨11809, true, false, [2019], [11]⟩,
        ⟨90, false, false, [2019, 79217], []⟩,
        ⟨11792, false, false, [2019], []⟩,
        ⟨11802, false, false, [], []⟩,
        ⟨11803, false, false, [], []⟩,
        ⟨11804, false, false, [], []⟩
      ]⟩,
    ⟨[2019, 77157, 1], [2019, 77159], .contexts [
        ⟨489, false, false, [2019], []⟩
      ]⟩,
    ⟨[2019, 77159], [2019, 77159], .contexts []⟩,
    ⟨[2019, 77159], [2019, 77159], .contexts []⟩,
    ⟨[2019, 77159], [2019, 77159], .contexts []⟩,
    ⟨[3189], [2019, 3155], .source 1659⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [3189, 79211], .contexts [
        ⟨12025, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨11789, false, false, [2019], [1, 5, 3, 1]⟩,
        ⟨11799, false, false, [], [1, 5, 3, 1]⟩,
        ⟨11800, false, false, [], [1, 5, 3, 1]⟩,
        ⟨12026, false, false, [], [5, 3, 1]⟩,
        ⟨12027, false, false, [], [5, 3, 1]⟩,
        ⟨12028, false, false, [], [5, 3, 1]⟩,
        ⟨12029, false, false, [], [5, 3, 1]⟩,
        ⟨11784, false, false, [2019], [3, 1]⟩,
        ⟨12030, true, false, [], [79215, 3, 1]⟩,
        ⟨11768, false, false, [3189], [1]⟩,
        ⟨11763, false, false, [3189], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 188. -/
def y322TCContextRaw188 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[3191], [3189, 2561], .source 1660⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [3191, 77675], .contexts [
        ⟨12031, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨11742, false, false, [3189], [13, 1, 11, 9]⟩,
        ⟨11720, false, false, [3189], [1, 11, 9]⟩,
        ⟨11687, false, false, [3189], [11, 9]⟩,
        ⟨11674, false, false, [3189], [9]⟩,
        ⟨10314, false, false, [3189], []⟩,
        ⟨12032, true, false, [], [77675]⟩
      ]⟩,
    ⟨[3193], [3191, 2189], .source 1661⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [3193, 2375, 79175], .contexts [
        ⟨12033, false, false, [], [1, 5]⟩,
        ⟨11523, false, false, [3191], [5]⟩,
        ⟨12034, true, false, [], [79175, 5]⟩,
        ⟨11510, true, false, [3193], [5]⟩,
        ⟨1479, false, false, [3193, 78989], []⟩,
        ⟨1481, false, false, [3193, 78989], []⟩,
        ⟨10221, false, false, [3193], [3, 5, 3]⟩,
        ⟨10490, false, false, [3193], [5, 3]⟩,
        ⟨10491, false, false, [3193], [5, 3]⟩,
        ⟨10492, false, false, [3193], [5, 3]⟩,
        ⟨10492, false, false, [3193], [5, 3]⟩,
        ⟨10202, true, false, [3193, 2375], [5, 3]⟩,
        ⟨49, false, false, [3193, 2375, 78989], [3]⟩,
        ⟨10196, false, false, [3193, 2375], [3]⟩,
        ⟨11507, false, false, [3193, 2375], []⟩,
        ⟨11511, false, false, [3193, 2375], []⟩,
        ⟨11512, true, false, [3193], [79175]⟩
      ]⟩,
    ⟨[3195], [3193, 2375], .source 1662⟩,
    ⟨[3197], [3195, 1887], .source 1663⟩,
    ⟨[3199], [3197, 1997], .source 1664⟩,
    ⟨[
      79351, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1
    ], [3199, 1899, 77681], .contexts [
        ⟨12035, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨12036, true, false, [], [79175, 3, 1, 15, 13, 1]⟩,
        ⟨11508, false, false, [3195], [1, 15, 13, 1]⟩,
        ⟨10194, false, false, [3195], [15, 13, 1]⟩,
        ⟨8442, false, false, [3195], [13, 1]⟩,
        ⟨12037, true, false, [], [78557, 13, 1]⟩,
        ⟨8436, false, false, [3197], [1]⟩,
        ⟨12038, true, false, [], [78557, 1]⟩,
        ⟨8444, false, false, [3199], []⟩
      ]⟩,
    ⟨[3201], [3199, 1899], .source 1665⟩,
    ⟨[3203], [3201, 1901], .source 1666⟩,
    ⟨[3205], [3203, 2003], .source 1667⟩,
    ⟨[3205, 78559], [3205, 78559], .contexts []⟩,
    ⟨[3205, 78559], [3205, 78559], .contexts []⟩,
    ⟨[79353, 5], [79353, 5], .contexts []⟩,
    ⟨[79353, 5], [3205, 78559], .contexts [
        ⟨12045, false, false, [], []⟩,
        ⟨11991, true, false, [], [5]⟩,
        ⟨11991, true, false, [], [5]⟩,
        ⟨11990, true, false, [], [5]⟩,
        ⟨11987, true, false, [], [5]⟩,
        ⟨1457, false, false, [79351], []⟩,
        ⟨1465, false, false, [79351], []⟩,
        ⟨12039, false, false, [], [11, 9, 1]⟩,
        ⟨12040, true, false, [], [77681, 11, 9, 1]⟩,
        ⟨8469, false, false, [3201], [9, 1]⟩,
        ⟨12041, true, false, [], [78561, 9, 1]⟩,
        ⟨8484, false, false, [3203], [1]⟩,
        ⟨12042, true, false, [], [78561, 1]⟩,
        ⟨8463, false, false, [3205], []⟩,
        ⟨12043, false, false, [], []⟩,
        ⟨12044, false, false, [], []⟩,
        ⟨8453, false, false, [3205], []⟩,
        ⟨24, true, false, [], [3205, 78559]⟩
      ]⟩,
    ⟨[3207], [3204], .source 1668⟩,
    ⟨[79353, 5], [3205, 78559], .contexts [
        ⟨12045, false, false, [], []⟩,
        ⟨12046, false, false, [], []⟩,
        ⟨12043, false, false, [], []⟩,
        ⟨12044, false, false, [], []⟩,
        ⟨12044, false, false, [], []⟩
      ]⟩,
    ⟨[3209], [3205, 1899], .source 1669⟩,
    ⟨[79353], [79353], .contexts []⟩,
    ⟨[77685, 11], [77685, 11], .contexts []⟩,
    ⟨[79353], [79353], .contexts []⟩,
    ⟨[3211], [3208], .source 1670⟩,
    ⟨[3208], [3208], .contexts []⟩,
    ⟨[77685, 11], [3211, 79353], .contexts [
        ⟨12051, false, false, [], []⟩,
        ⟨12049, false, false, [3208], [77685, 11]⟩,
        ⟨8429, true, false, [3208, 3205], [11]⟩,
        ⟨8447, true, false, [3208, 3205], [5, 11]⟩,
        ⟨12048, true, false, [3208], [11, 5, 11]⟩,
        ⟨7381, false, false, [3208, 79353], []⟩,
        ⟨12050, false, false, [3208], []⟩,
        ⟨12052, false, false, [3208], []⟩,
        ⟨12054, true, false, [], [79353]⟩,
        ⟨12054, true, false, [], [79353]⟩,
        ⟨12053, true, false, [], [79353]⟩
      ]⟩,
    ⟨[3213], [3205, 1997], .source 1671⟩,
    ⟨[3215], [3213, 3207], .source 1672⟩,
    ⟨[79353, 13], [79353, 13], .contexts []⟩,
    ⟨[3217], [3214], .source 1673⟩,
    ⟨[3214], [3214], .contexts []⟩,
    ⟨[3219], [3205, 1885], .source 1674⟩,
    ⟨[3219, 79031], [3219, 79031], .contexts []⟩,
    ⟨[3221], [3218], .source 1675⟩,
    ⟨[3218], [3218], .contexts []⟩,
    ⟨[79353, 15], [3219, 79031], .contexts [
        ⟨12063, false, false, [3220], [79353, 15]⟩,
        ⟨12064, false, false, [3220], [79353, 15]⟩,
        ⟨12064, false, false, [3220], [79353, 15]⟩,
        ⟨12052, true, false, [3220, 3218], [15]⟩,
        ⟨12050, true, false, [3220, 3218], [15]⟩,
        ⟨1504, true, false, [3220, 3218, 79353], [15]⟩,
        ⟨12048, false, false, [3220, 3218], [15, 5, 15, 15]⟩,
        ⟨8459, false, false, [3220, 3218, 3205], [5, 15, 15]⟩,
        ⟨12061, true, false, [3220, 3218], [77145, 5, 15, 15]⟩,
        ⟨10470, true, false, [3220], [5, 15, 15]⟩,
        ⟨49, false, false, [3220, 79031], [15, 15]⟩,
        ⟨10466, false, false, [3220], [15, 15]⟩,
        ⟨12062, false, false, [3220, 3218], [15, 15]⟩,
        ⟨3, false, false, [3220, 79031], []⟩,
        ⟨12063, false, true, [], [79031]⟩
      ]⟩,
    ⟨[3211, 79353], [3211, 79353], .contexts []⟩,
    ⟨[79351, 11], [79351, 11], .contexts []⟩,
    ⟨[3223], [3209, 3111], .source 1676⟩,
    ⟨[79351, 11], [3223, 77321], .contexts [
        ⟨12067, false, false, [], []⟩,
        ⟨11989, true, false, [], [11]⟩,
        ⟨12066, true, false, [3210], [3, 11]⟩,
        ⟨12066, true, false, [3210], [3, 11]⟩,
        ⟨12055, true, false, [3210], [3, 11]⟩,
        ⟨12051, true, false, [3210], [3, 11]⟩,
        ⟨1040, false, false, [3210, 77685], []⟩,
        ⟨36, false, false, [3210, 77685], []⟩,
        ⟨5722, false, false, [3210], []⟩,
        ⟨5724, false, false, [3210], []⟩,
        ⟨7574, false, false, [3210, 1299], []⟩,
        ⟨11584, true, false, [3210], [77321]⟩,
        ⟨12053, false, true, [], [3111, 77321]⟩,
        ⟨12068, true, false, [], [77321]⟩
      ]⟩,
    ⟨[3225], [3222], .source 1677⟩,
    ⟨[77321, 11], [3225, 79351], .contexts [
        ⟨12069, true, false, [3222], [11]⟩,
        ⟨90, false, false, [3222, 79351], []⟩,
        ⟨12070, true, false, [], [79351]⟩
      ]⟩,
    ⟨[3217, 79353], [3217, 79353], .contexts []⟩,
    ⟨[79353, 13], [3217, 79353], .contexts [
        ⟨12058, false, false, [], []⟩,
        ⟨12058, false, false, [], []⟩,
        ⟨12057, false, false, [3214], [79353, 13]⟩,
        ⟨12047, false, false, [3214, 3213], [79353, 13]⟩,
        ⟨49, true, false, [3214, 3213, 3204, 79353], [13]⟩,
        ⟨12046, false, false, [3214, 3213, 3204], [5, 13]⟩,
        ⟨12056, false, false, [3214], [78559, 5, 13]⟩,
        ⟨8454, true, false, [3214, 3205], [5, 13]⟩,
        ⟨12048, true, false, [3214], [13, 5, 13]⟩,
        ⟨8416, false, false, [3214, 79353], []⟩,
        ⟨12050, false, false, [3214], []⟩,
        ⟨12052, false, false, [3214], []⟩,
        ⟨12060, true, false, [], [79353]⟩,
        ⟨12060, true, false, [], [79353]⟩,
        ⟨12059, true, false, [], [79353]⟩,
        ⟨12072, false, false, [], []⟩,
        ⟨12072, false, false, [], []⟩
      ]⟩,
    ⟨[79351], [79351], .contexts []⟩,
    ⟨[3216], [3216], .contexts []⟩,
    ⟨[3223, 77321], [3223, 77321], .contexts []⟩,
    ⟨[3223, 77321], [3223, 77321], .contexts []⟩,
    ⟨[3227], [3223, 1759], .source 1678⟩,
    ⟨[3229], [3227, 3225], .source 1679⟩,
    ⟨[3229, 79349], [3229, 79349], .contexts []⟩,
    ⟨[79351], [3229, 79349], .contexts [
        ⟨12074, false, false, [], []⟩,
        ⟨991, true, false, [79351], []⟩,
        ⟨12067, false, false, [], [1, 11, 1]⟩,
        ⟨12069, false, false, [], [1, 11, 1]⟩,
        ⟨12076, false, false, [], [1, 11, 1]⟩,
        ⟨12077, false, false, [], [1, 11, 1]⟩,
        ⟨12077, false, false, [], [1, 11, 1]⟩,
        ⟨1296, false, false, [3223], [11, 1]⟩,
        ⟨7574, false, false, [3223], [11, 1]⟩,
        ⟨12078, true, false, [], [77321, 11, 1]⟩,
        ⟨12071, false, false, [3227], [1]⟩,
        ⟨12079, true, false, [], [79351, 1]⟩,
        ⟨11985, false, false, [3229], []⟩,
        ⟨12080, false, false, [], []⟩
      ]⟩,
    ⟨[3231], [3228], .source 1680⟩,
    ⟨[3228], [3228], .contexts []⟩,
    ⟨[3233], [3231, 3223], .source 1681⟩,
    ⟨[79351], [3229, 79349], .contexts [
        ⟨12081, false, false, [], []⟩,
        ⟨12080, false, false, [], []⟩
      ]⟩,
    ⟨[3235], [3231, 3215], .source 1682⟩,
    ⟨[3237], [3235, 3229], .source 1683⟩,
    ⟨[3233, 77321], [3233, 77321], .contexts []⟩,
    ⟨[3239], [3233, 3115], .source 1684⟩,
    ⟨[79349, 15], [79347], .contexts [
        ⟨11992, false, false, [], []⟩,
        ⟨11993, false, false, [], []⟩,
        ⟨11981, false, false, [], []⟩,
        ⟨11981, false, false, [], []⟩
      ]⟩,
    ⟨[79183, 11], [79183, 11], .contexts []⟩,
    ⟨[79183, 11], [3238, 79347], .contexts [
        ⟨12089, false, false, [3238], [79183, 11]⟩,
        ⟨11590, true, false, [3238, 3233], [11]⟩,
        ⟨12088, true, false, [3238], [15, 11]⟩,
        ⟨12088, true, false, [3238], [15, 11]⟩,
        ⟨12084, false, false, [3238], [77321, 15, 11]⟩,
        ⟨12082, false, false, [3238], [3223, 77321, 15, 11]⟩,
        ⟨12076, true, false, [3238, 3228], [15, 11]⟩,
        ⟨12069, true, false, [3238, 3228], [15, 11]⟩,
        ⟨12081, false, false, [3238, 3228], [11, 15, 11]⟩,
        ⟨1054, false, false, [3238, 79349], []⟩,
        ⟨20, false, false, [3238, 79349], []⟩,
        ⟨12090, false, false, [3238], []⟩
      ]⟩,
    ⟨[3241], [3238], .source 1685⟩,
    ⟨[3238], [3238], .contexts []⟩,
    ⟨[3241], [3238], .contexts [
        ⟨12093, false, false, [], []⟩,
        ⟨12094, false, false, [], []⟩,
        ⟨12094, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 189. -/
def y322TCContextRaw189 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[79183, 11], [3241, 79347], .contexts [
        ⟨12091, false, false, [], []⟩,
        ⟨12092, false, false, [], []⟩,
        ⟨12095, true, false, [], [79347]⟩
      ]⟩,
    ⟨[3239], [3240], .contexts [
        ⟨12093, true, true, [], []⟩
      ]⟩,
    ⟨[3237, 79349], [3237, 79349], .contexts []⟩,
    ⟨[79349, 13, 15], [3237, 79349, 15], .contexts [
        ⟨12081, true, false, [3228], [13, 15]⟩,
        ⟨11989, true, false, [3228], [13, 15]⟩,
        ⟨12073, true, false, [3228, 3216], [3, 13, 15]⟩,
        ⟨1881, false, false, [3228, 3216, 79353], [15]⟩,
        ⟨36, false, false, [3228, 3216, 79353], [15]⟩,
        ⟨11989, false, false, [3228, 3216], [15]⟩,
        ⟨11988, false, false, [3228, 3216], [15]⟩,
        ⟨11988, false, false, [3228, 3216], [15]⟩,
        ⟨12074, false, false, [3228, 3216], [15]⟩,
        ⟨12075, true, false, [3228], [79351, 15]⟩,
        ⟨12075, true, false, [3228], [79351, 15]⟩,
        ⟨12059, false, true, [3228], [79351, 15]⟩,
        ⟨12085, false, false, [3228, 3215], [15]⟩,
        ⟨12082, true, false, [], [3215, 3229, 79349, 15]⟩,
        ⟨12086, true, false, [], [3229, 79349, 15]⟩,
        ⟨12087, true, false, [], [79349, 15]⟩,
        ⟨12098, false, false, [], [15]⟩,
        ⟨12098, false, false, [], [15]⟩
      ]⟩,
    ⟨[79345], [79345], .contexts []⟩,
    ⟨[3243], [3236], .source 1686⟩,
    ⟨[3236], [3236], .contexts []⟩,
    ⟨[3231, 79353], [3231, 79353], .contexts []⟩,
    ⟨[3245], [3231, 3219], .source 1687⟩,
    ⟨[3241, 79347], [3241, 79347], .contexts []⟩,
    ⟨[3241, 79347], [3241, 79347], .contexts []⟩,
    ⟨[79183, 11], [3241, 79347], .contexts [
        ⟨12091, false, false, [], []⟩,
        ⟨12096, false, false, [], []⟩,
        ⟨12105, false, false, [], []⟩,
        ⟨12106, false, false, [], []⟩,
        ⟨12106, false, false, [], []⟩
      ]⟩,
    ⟨[79347, 5], [79347, 5], .contexts []⟩,
    ⟨[3239], [3240], .contexts [
        ⟨12097, false, false, [], []⟩
      ]⟩,
    ⟨[3240], [3240], .contexts []⟩,
    ⟨[3241, 79345], [3241, 79345], .contexts []⟩,
    ⟨[3241, 79345], [3241, 79345], .contexts []⟩,
    ⟨[79183, 13], [3105, 77441], .contexts [
        ⟨11581, false, false, [3106], [79183, 13]⟩,
        ⟨11582, false, false, [3106], [79183, 13]⟩,
        ⟨11582, false, false, [3106], [79183, 13]⟩,
        ⟨11569, true, false, [3106, 3104], [13]⟩,
        ⟨11580, true, false, [3106, 3104], [13]⟩,
        ⟨3290, true, false, [3106, 3104, 79183], [13]⟩,
        ⟨11577, false, false, [3106, 3104], [13, 3, 13, 13]⟩,
        ⟨9651, false, false, [3106, 3104, 3099], [3, 13, 13]⟩,
        ⟨11578, true, false, [3106, 3104], [77573, 3, 13, 13]⟩,
        ⟨11111, false, false, [3106, 3104, 3103], [13, 13]⟩,
        ⟨11579, true, false, [3106, 3104], [77441, 13, 13]⟩,
        ⟨98, false, false, [3106, 77441], []⟩,
        ⟨11581, false, true, [], [77441]⟩
      ]⟩,
    ⟨[3105, 77441], [3105, 77441], .contexts []⟩,
    ⟨[79345, 11], [79345, 11], .contexts []⟩,
    ⟨[3249], [3239, 3105], .source 1689⟩,
    ⟨[79345, 11], [3249, 77441], .contexts [
        ⟨12115, false, false, [], []⟩,
        ⟨12112, true, false, [3240], [11]⟩,
        ⟨12111, true, false, [3240], [11]⟩,
        ⟨11979, true, false, [], [11]⟩,
        ⟨12107, true, false, [3240], [13, 11]⟩,
        ⟨1060, false, false, [3240, 79183], []⟩,
        ⟨108, false, false, [3240, 79183], []⟩,
        ⟨12113, false, false, [3240], []⟩,
        ⟨12114, false, false, [3240], []⟩,
        ⟨12114, false, false, [3240], []⟩,
        ⟨3513, false, false, [3240, 3105], []⟩,
        ⟨12109, true, false, [], [3105, 77441]⟩,
        ⟨12116, true, false, [], [77441]⟩
      ]⟩,
    ⟨[3251], [3248], .source 1690⟩,
    ⟨[79345, 1], [79343], .contexts [
        ⟨11996, false, false, [], []⟩,
        ⟨11997, false, false, [], []⟩,
        ⟨11975, false, false, [], []⟩,
        ⟨11975, false, false, [], []⟩
      ]⟩,
    ⟨[79345, 0], [79345, 1], .contexts [
        ⟨19, false, false, [79345], []⟩
      ]⟩,
    ⟨[79343], [79343], .contexts []⟩,
    ⟨[3239, 78747], [3239, 78747], .contexts []⟩,
    ⟨[3239, 78749], [3239, 78749], .contexts []⟩,
    ⟨[79347, 5, 13], [3239, 78749], .contexts [
        ⟨12108, false, false, [], [13]⟩,
        ⟨12108, false, false, [], [13]⟩,
        ⟨12107, true, false, [3240], [5, 13]⟩,
        ⟨1083, false, false, [3240, 79183], [13]⟩,
        ⟨1084, false, false, [3240, 79183], [13]⟩,
        ⟨11566, false, false, [3240], [11, 13]⟩,
        ⟨9345, false, false, [3240], [11, 13]⟩,
        ⟨9346, false, false, [3240], [11, 13]⟩,
        ⟨9346, false, false, [3240], [11, 13]⟩,
        ⟨9361, false, false, [3240], [13]⟩,
        ⟨9362, false, false, [3240], [13]⟩,
        ⟨9363, false, false, [3240], [13]⟩,
        ⟨9363, false, false, [3240], [13]⟩,
        ⟨9368, false, false, [3240], [13]⟩,
        ⟨12110, true, false, [], [78747, 13]⟩,
        ⟨12110, true, false, [], [78747, 13]⟩,
        ⟨12109, true, false, [], [78747, 13]⟩,
        ⟨12122, false, false, [], [13]⟩,
        ⟨12122, false, false, [], [13]⟩,
        ⟨9371, false, false, [3239], []⟩,
        ⟨12123, false, false, [], []⟩
      ]⟩,
    ⟨[3239, 78749], [3239, 78749], .contexts []⟩,
    ⟨[78749, 5], [78749, 5], .contexts []⟩,
    ⟨[78749, 5], [3241, 79345], .contexts [
        ⟨12126, false, false, [], []⟩,
        ⟨12125, true, false, [3238], [5]⟩,
        ⟨12124, true, false, [3238], [5]⟩,
        ⟨1578, false, false, [3238, 79347], []⟩,
        ⟨108, false, false, [3238, 79347], []⟩,
        ⟨11994, false, false, [3238], []⟩,
        ⟨11995, false, false, [3238], []⟩,
        ⟨11978, false, false, [3238], []⟩,
        ⟨11978, false, false, [3238], []⟩,
        ⟨12100, false, false, [3238], []⟩,
        ⟨12095, true, false, [], [79345]⟩
      ]⟩,
    ⟨[79345, 5], [3239, 78749], .contexts [
        ⟨12127, true, false, [3240], [5]⟩,
        ⟨49, false, false, [3240, 78749], []⟩,
        ⟨12097, true, false, [], [78749]⟩
      ]⟩,
    ⟨[3249, 77441], [3249, 77441], .contexts []⟩,
    ⟨[3249, 77439], [3249, 77439], .contexts []⟩,
    ⟨[3249, 77439], [3249, 77439], .contexts []⟩,
    ⟨[77439, 11], [77439, 11], .contexts []⟩,
    ⟨[3248], [3248], .contexts []⟩,
    ⟨[77439, 11], [3251, 79343], .contexts [
        ⟨12132, false, false, [], []⟩,
        ⟨12131, true, false, [3248], [11]⟩,
        ⟨12130, true, false, [3248], [11]⟩,
        ⟨2232, true, false, [], [11]⟩,
        ⟨12129, true, false, [3248], [1, 11]⟩,
        ⟨12129, true, false, [3248], [1, 11]⟩,
        ⟨12117, true, false, [3248], [1, 11]⟩,
        ⟨12115, true, false, [3248], [1, 11]⟩,
        ⟨1000, false, false, [3248, 79345], []⟩,
        ⟨12120, false, false, [3248], []⟩,
        ⟨12119, false, false, [3248], []⟩,
        ⟨12121, false, false, [3248], []⟩,
        ⟨12133, true, false, [], [79343]⟩,
        ⟨12133, true, false, [], [79343]⟩,
        ⟨12118, true, false, [], [79343]⟩
      ]⟩,
    ⟨[3249], [3250], .contexts [
        ⟨12118, true, true, [], []⟩
      ]⟩,
    ⟨[3249], [3249], .contexts []⟩,
    ⟨[3253], [3249, 2657], .source 1691⟩,
    ⟨[3255], [3252], .source 1692⟩,
    ⟨[3255], [3252], .contexts [
        ⟨12138, false, false, [], []⟩,
        ⟨24, false, false, [3252], []⟩
      ]⟩,
    ⟨[3253], [3254], .contexts [
        ⟨12138, true, true, [], []⟩
      ]⟩,
    ⟨[79339], [3253, 78233], .contexts [
        ⟨12139, false, false, [3254], [79339]⟩,
        ⟨12001, true, false, [3254, 3252], []⟩,
        ⟨11971, true, false, [3254, 3252], []⟩,
        ⟨11973, true, false, [3254, 3252], [9]⟩,
        ⟨11973, true, false, [3254, 3252], [9]⟩,
        ⟨11999, true, false, [3254, 3252], [9]⟩,
        ⟨11998, true, false, [3254, 3252], [9]⟩,
        ⟨12134, true, false, [3254, 3252, 3250], [11, 9]⟩,
        ⟨90, false, false, [3254, 3252, 3250, 77439], [9]⟩,
        ⟨12135, true, false, [3254, 3252], [77439, 9]⟩,
        ⟨12130, false, false, [3254, 3252], [9]⟩,
        ⟨12136, true, false, [3254, 3252], [77439, 9]⟩,
        ⟨12131, false, false, [3254, 3252], [9]⟩,
        ⟨11100, false, false, [3254, 3252, 3249], []⟩,
        ⟨12137, true, false, [3254, 3252], [78233]⟩,
        ⟨12140, true, false, [], [78233]⟩
      ]⟩,
    ⟨[3253, 78235], [3253, 78235], .contexts []⟩,
    ⟨[3257], [3253, 2763], .source 1693⟩,
    ⟨[3257, 77881], [79335], .contexts [
        ⟨12143, false, false, [], [77881]⟩,
        ⟨11081, true, false, [3253], []⟩,
        ⟨12142, true, false, [], [5]⟩,
        ⟨12140, false, false, [], [78235, 5]⟩,
        ⟨12142, true, false, [3254, 3252], [5]⟩,
        ⟨6494, true, false, [3254], [5]⟩,
        ⟨12141, true, false, [3254, 3252], [1, 5]⟩,
        ⟨11968, false, false, [3254, 3252], [5]⟩,
        ⟨12002, false, false, [3254, 3252], [5]⟩,
        ⟨12139, true, false, [3254], [79337, 5]⟩,
        ⟨11965, false, false, [], []⟩
      ]⟩,
    ⟨[3259], [3256], .source 1694⟩,
    ⟨[3259], [3256], .contexts [
        ⟨12145, false, false, [], []⟩
      ]⟩,
    ⟨[79335], [3257, 77881], .contexts [
        ⟨12146, false, false, [3258], [79335]⟩,
        ⟨24, false, false, [3258, 3256], [79335]⟩,
        ⟨12003, true, false, [3258, 3256], []⟩,
        ⟨12144, true, false, [3258, 3256], []⟩,
        ⟨12145, false, true, [], [77881]⟩
      ]⟩,
    ⟨[3256], [3256], .contexts []⟩,
    ⟨[77881, 3], [3259, 79333], .contexts [
        ⟨12147, true, false, [3256], [3]⟩,
        ⟨11962, false, false, [3256], []⟩,
        ⟨12004, false, false, [3256], []⟩,
        ⟨12148, true, false, [], [79333]⟩,
        ⟨12148, true, false, [], [79333]⟩,
        ⟨12146, true, false, [], [79333]⟩
      ]⟩,
    ⟨[3261], [3241, 3243], .source 1695⟩,
    ⟨[78749, 5, 15], [3261, 79345], .contexts [
        ⟨12126, false, false, [], [15]⟩,
        ⟨12127, false, false, [], [15]⟩,
        ⟨12111, false, false, [], [15]⟩,
        ⟨12112, false, false, [], [15]⟩,
        ⟨12112, false, false, [], [15]⟩,
        ⟨11979, true, false, [3241], [15]⟩,
        ⟨11982, true, false, [3241], [13, 15]⟩,
        ⟨12099, true, false, [3241, 3236], [13, 15]⟩,
        ⟨3449, false, false, [3241, 3236, 79349], []⟩,
        ⟨149, false, false, [3241, 3236, 79349], []⟩,
        ⟨12090, false, false, [3241, 3236], [13]⟩,
        ⟨11994, false, false, [3241, 3236], []⟩,
        ⟨11995, false, false, [3241, 3236], []⟩,
        ⟨11978, false, false, [3241, 3236], []⟩,
        ⟨11978, false, false, [3241, 3236], []⟩,
        ⟨12100, false, false, [3241, 3236], []⟩,
        ⟨12102, true, false, [3241], [79345]⟩,
        ⟨12102, true, false, [3241], [79345]⟩,
        ⟨12101, true, false, [3241], [79345]⟩,
        ⟨12150, true, false, [], [79345]⟩
      ]⟩,
    ⟨[3263], [3261, 3239], .source 1696⟩,
    ⟨[3265], [3262], .source 1697⟩,
    ⟨[3264], [3264], .contexts []⟩,
    ⟨[78749, 1], [3263, 78753], .contexts [
        ⟨12153, false, false, [3264], [78749, 1]⟩,
        ⟨289, true, false, [3264, 3262, 78749], [1]⟩,
        ⟨12151, false, false, [3264, 3262], [5, 15, 1]⟩,
        ⟨12128, false, false, [3264, 3262, 3261], [15, 1]⟩,
        ⟨12152, true, false, [3264, 3262], [78749, 15, 1]⟩,
        ⟨9373, false, false, [3264], [1]⟩,
        ⟨9376, false, false, [3264], []⟩,
        ⟨9518, false, false, [3264], []⟩,
        ⟨12154, true, false, [], [78753]⟩,
        ⟨12154, true, false, [], [78753]⟩,
        ⟨12153, false, true, [], [78753]⟩
      ]⟩,
    ⟨[3267], [3239, 3263], .source 1698⟩,
    ⟨[78753, 5], [78753, 5], .contexts []⟩,
    ⟨[3269], [3266], .source 1699⟩,
    ⟨[3266], [3266], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 190. -/
def y322TCContextRaw190 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78753, 5], [3269, 79343], .contexts [
        ⟨12157, false, false, [], []⟩,
        ⟨12156, false, false, [3266], [78753, 5]⟩,
        ⟨12155, true, false, [3266, 3239], [5]⟩,
        ⟨12125, true, false, [3266], [1, 5]⟩,
        ⟨12125, true, false, [3266], [1, 5]⟩,
        ⟨12123, true, false, [3266], [1, 5]⟩,
        ⟨12128, true, false, [3266], [1, 5]⟩,
        ⟨1509, false, false, [3266, 79345], []⟩,
        ⟨12120, false, false, [3266], []⟩,
        ⟨12119, false, false, [3266], []⟩,
        ⟨12121, false, false, [3266], []⟩,
        ⟨12159, true, false, [], [79343]⟩,
        ⟨12159, true, false, [], [79343]⟩,
        ⟨12158, true, false, [], [79343]⟩
      ]⟩,
    ⟨[79343, 5], [3267, 78753], .contexts [
        ⟨12160, true, false, [3268], [5]⟩,
        ⟨49, false, false, [3268, 78753], []⟩,
        ⟨12158, false, true, [], [78753]⟩
      ]⟩,
    ⟨[3251, 79343], [3251, 79343], .contexts []⟩,
    ⟨[77439, 11], [3251, 79343], .contexts [
        ⟨12132, false, false, [], []⟩,
        ⟨12134, false, false, [], []⟩,
        ⟨12162, false, false, [], []⟩,
        ⟨12162, false, false, [], []⟩
      ]⟩,
    ⟨[3271], [3251, 3267], .source 1700⟩,
    ⟨[78753, 11], [78753, 11], .contexts []⟩,
    ⟨[3273], [3270], .source 1701⟩,
    ⟨[3270], [3270], .contexts []⟩,
    ⟨[78753, 11], [3273, 77437], .contexts [
        ⟨12165, false, false, [], []⟩,
        ⟨12164, false, false, [3270], [78753, 11]⟩,
        ⟨12161, true, false, [3270, 3251], [11]⟩,
        ⟨12163, true, false, [3270], [5, 11]⟩,
        ⟨1028, false, false, [3270, 77439], []⟩,
        ⟨3533, false, false, [3270], []⟩,
        ⟨3531, false, false, [3270], []⟩,
        ⟨3535, false, false, [3270], []⟩,
        ⟨12167, true, false, [], [77437]⟩,
        ⟨12167, true, false, [], [77437]⟩,
        ⟨12166, true, false, [], [77437]⟩
      ]⟩,
    ⟨[3271], [3272], .contexts [
        ⟨12166, true, true, [], []⟩
      ]⟩,
    ⟨[77439, 9], [2657, 78233], .contexts [
        ⟨11100, false, false, [], []⟩
      ]⟩,
    ⟨[3275], [2657, 2783], .source 1702⟩,
    ⟨[3277], [3275, 2659], .source 1703⟩,
    ⟨[3279], [3277, 3251], .source 1704⟩,
    ⟨[79343, 9], [3250, 3279, 79343], .contexts [
        ⟨12163, true, false, [3250], [9]⟩,
        ⟨344, false, false, [3250, 77439], []⟩,
        ⟨346, false, false, [3250, 77439], []⟩,
        ⟨12170, false, false, [3250], [11, 9, 11]⟩,
        ⟨11094, false, false, [3250], [11, 9, 11]⟩,
        ⟨11095, false, false, [3250], [11, 9, 11]⟩,
        ⟨11095, false, false, [3250], [11, 9, 11]⟩,
        ⟨11106, false, false, [3250, 2657], [9, 11]⟩,
        ⟨12171, true, false, [3250], [78233, 9, 11]⟩,
        ⟨11099, false, false, [3250, 3275], [11]⟩,
        ⟨12172, true, false, [3250], [77439, 11]⟩,
        ⟨12134, false, false, [3250, 3277], []⟩,
        ⟨12173, true, false, [3250], [79343]⟩,
        ⟨12121, false, false, [3250, 3279], []⟩
      ]⟩,
    ⟨[3281], [3249, 3279], .source 1705⟩,
    ⟨[1917, 78235], [1917, 78235], .contexts []⟩,
    ⟨[3283], [1917, 2763], .source 1706⟩,
    ⟨[78235, 3, 5], [3283, 77881], .contexts [
        ⟨8181, false, false, [], [5]⟩,
        ⟨8181, false, false, [], [5]⟩,
        ⟨6500, true, false, [], [3, 5]⟩,
        ⟨8180, true, false, [1920], [9, 3, 5]⟩,
        ⟨1010, false, false, [1920, 78237], [5]⟩,
        ⟨6722, false, false, [1920], [5]⟩,
        ⟨6721, false, false, [1920], [5]⟩,
        ⟨6724, false, false, [1920], [5]⟩,
        ⟨8182, true, false, [], [78235, 5]⟩,
        ⟨8182, true, false, [], [78235, 5]⟩,
        ⟨8155, false, true, [], [78235, 5]⟩,
        ⟨12176, false, false, [], [5]⟩,
        ⟨12176, false, false, [], [5]⟩,
        ⟨11081, false, false, [1917], []⟩,
        ⟨12177, true, false, [], [77881]⟩
      ]⟩,
    ⟨[3285], [3283, 3259], .source 1707⟩,
    ⟨[3287], [2763, 3259], .source 1708⟩,
    ⟨[79333, 5], [79333, 5], .contexts []⟩,
    ⟨[79333], [79333], .contexts []⟩,
    ⟨[3289], [3284], .source 1709⟩,
    ⟨[3291], [3289, 3287], .source 1710⟩,
    ⟨[3259, 79333], [3259, 79333], .contexts []⟩,
    ⟨[77881, 3], [3259, 79333], .contexts [
        ⟨12149, false, false, [], []⟩,
        ⟨12185, false, false, [], []⟩,
        ⟨12185, false, false, [], []⟩
      ]⟩,
    ⟨[77881, 2], [77881, 3], .contexts [
        ⟨36, false, false, [77881], []⟩
      ]⟩,
    ⟨[79161, 13], [79161, 13], .contexts []⟩,
    ⟨[3293], [2801, 3259], .source 1711⟩,
    ⟨[79161, 13], [3293, 79333], .contexts [
        ⟨12188, false, false, [], []⟩,
        ⟨11117, false, false, [2798], [79161, 13]⟩,
        ⟨11044, true, false, [2798, 2741], [13]⟩,
        ⟨11050, true, false, [2798], [3, 13]⟩,
        ⟨11050, true, false, [2798], [3, 13]⟩,
        ⟨11050, true, false, [2798], [3, 13]⟩,
        ⟨11049, true, false, [2798], [3, 13]⟩,
        ⟨5236, true, false, [2798], [3, 13]⟩,
        ⟨1881, false, false, [2798, 77881], []⟩,
        ⟨12187, false, false, [2798], []⟩,
        ⟨12186, false, false, [2798], []⟩,
        ⟨12182, false, false, [2798, 3259], []⟩,
        ⟨11119, true, false, [], [3259, 79333]⟩,
        ⟨12189, true, false, [], [79333]⟩
      ]⟩,
    ⟨[3295], [3292], .source 1712⟩,
    ⟨[3297], [2865, 3259], .source 1713⟩,
    ⟨[79333, 15], [79333, 15], .contexts []⟩,
    ⟨[3299], [3296], .source 1714⟩,
    ⟨[3301], [3299, 3259], .source 1715⟩,
    ⟨[3309], [2761, 2869], .source 1719⟩,
    ⟨[3311], [3309, 2879], .source 1720⟩,
    ⟨[78225, 3], [78225, 3], .contexts []⟩,
    ⟨[79331], [79331], .contexts []⟩,
    ⟨[3313], [3310], .source 1721⟩,
    ⟨[3315], [3313, 3259], .source 1722⟩,
    ⟨[78225, 3], [3315, 79331], .contexts [
        ⟨12198, false, false, [], []⟩,
        ⟨12197, false, false, [3310], [78225, 3]⟩,
        ⟨11193, true, false, [3310, 3309], [3]⟩,
        ⟨5003, true, false, [3310, 3309], [1, 3]⟩,
        ⟨12196, false, false, [3310], [77885, 3, 1, 3]⟩,
        ⟨11188, true, false, [3310, 2761], [3, 1, 3]⟩,
        ⟨11176, true, false, [3310], [3, 1, 3]⟩,
        ⟨852, false, false, [3310, 77881], []⟩,
        ⟨853, false, false, [3310, 77881], []⟩,
        ⟨12186, false, false, [3310], [1]⟩,
        ⟨11958, false, false, [3310, 3259], []⟩,
        ⟨12199, false, false, [3310, 3259], []⟩,
        ⟨12200, true, false, [], [3259, 79331]⟩,
        ⟨12201, true, false, [], [79331]⟩
      ]⟩,
    ⟨[3317], [3314], .source 1723⟩,
    ⟨[3269, 79343], [3269, 79343], .contexts []⟩,
    ⟨[3325], [3269, 3281], .source 1727⟩,
    ⟨[3327], [3325, 3267], .source 1728⟩,
    ⟨[3327, 78753, 9], [78753], .contexts [
        ⟨12206, false, false, [], [78753, 9]⟩,
        ⟨12161, true, false, [3325], [9]⟩,
        ⟨12205, false, false, [], [79343, 5, 9]⟩,
        ⟨12175, false, false, [3269], [79343, 5, 9]⟩,
        ⟨12136, false, false, [3269], [3279, 79343, 5, 9]⟩,
        ⟨12135, false, false, [3269], [3279, 79343, 5, 9]⟩,
        ⟨12174, true, false, [3269], [5, 9]⟩,
        ⟨12204, true, false, [], [9, 5, 9]⟩,
        ⟨12204, true, false, [], [9, 5, 9]⟩,
        ⟨12160, true, false, [], [9, 5, 9]⟩,
        ⟨12157, true, false, [], [9, 5, 9]⟩,
        ⟨1497, false, false, [78753], []⟩
      ]⟩,
    ⟨[3329], [3326], .source 1729⟩,
    ⟨[3326], [3326], .contexts []⟩,
    ⟨[3273, 77437], [3273, 77437], .contexts []⟩,
    ⟨[3273, 77435], [3273, 77435], .contexts []⟩,
    ⟨[3272], [3272], .contexts []⟩,
    ⟨[77435, 11], [3271, 78755], .contexts [
        ⟨12211, true, false, [3272], [11]⟩,
        ⟨2225, true, false, [], [11]⟩,
        ⟨12210, true, false, [3272], [3, 11]⟩,
        ⟨12210, true, false, [3272], [3, 11]⟩,
        ⟨12168, true, false, [3272], [3, 11]⟩,
        ⟨12165, true, false, [3272], [3, 11]⟩,
        ⟨1040, false, false, [3272, 78753], []⟩,
        ⟨36, false, false, [3272, 78753], []⟩,
        ⟨9379, false, false, [3272], []⟩,
        ⟨9516, false, false, [3272], []⟩,
        ⟨9382, false, false, [3272], []⟩,
        ⟨9382, false, false, [3272], []⟩,
        ⟨12212, true, false, [], [78755]⟩,
        ⟨12212, true, false, [], [78755]⟩,
        ⟨12169, true, false, [], [78755]⟩
      ]⟩,
    ⟨[3291, 79333], [3291, 79333], .contexts []⟩,
    ⟨[79333, 5, 1], [3291, 79331], .contexts [
        ⟨12181, false, false, [], [1]⟩,
        ⟨12181, false, false, [], [1]⟩,
        ⟨12179, false, false, [3284], [79333, 5, 1]⟩,
        ⟨12149, true, false, [3284, 3283], [5, 1]⟩,
        ⟨12178, true, false, [3284], [3, 5, 1]⟩,
        ⟨4744, false, false, [3284, 78235], [1]⟩,
        ⟨766, false, false, [3284, 78235], [1]⟩,
        ⟨11081, false, false, [3284], [3, 1]⟩,
        ⟨11107, false, false, [3284], [3, 1]⟩,
        ⟨11107, false, false, [3284], [3, 1]⟩,
        ⟨12149, false, false, [3284, 2763], [1]⟩,
        ⟨12180, true, false, [3284], [79333, 1]⟩,
        ⟨12182, false, false, [3284, 3287], [1]⟩,
        ⟨12183, true, false, [], [3287, 79333, 1]⟩,
        ⟨12184, true, false, [], [79333, 1]⟩,
        ⟨12214, false, false, [], [1]⟩,
        ⟨12214, false, false, [], [1]⟩,
        ⟨11958, false, false, [3291], []⟩
      ]⟩,
    ⟨[79333, 1], [79331], .contexts [
        ⟨12005, false, false, [], []⟩,
        ⟨12006, false, false, [], []⟩,
        ⟨11957, false, false, [], []⟩,
        ⟨11957, false, false, [], []⟩
      ]⟩,
    ⟨[3331], [3290], .source 1730⟩,
    ⟨[3290], [3290], .contexts []⟩,
    ⟨[3293, 79333], [3293, 79333], .contexts []⟩,
    ⟨[3293, 79333], [3293, 79333], .contexts []⟩,
    ⟨[3333], [2827, 1369], .source 1731⟩,
    ⟨[3335], [3295, 3333], .source 1732⟩,
    ⟨[79331, 13], [3335, 78097], .contexts [
        ⟨11958, true, false, [], [13]⟩,
        ⟨12220, true, false, [3292], [1, 13]⟩,
        ⟨12220, true, false, [3292], [1, 13]⟩,
        ⟨12219, true, false, [3292], [1, 13]⟩,
        ⟨12190, true, false, [3292], [1, 13]⟩,
        ⟨12188, true, false, [3292], [1, 13]⟩,
        ⟨3338, false, false, [3292, 79161], []⟩,
        ⟨389, false, false, [3292, 79161], []⟩,
        ⟨11168, false, false, [3292], [13, 1]⟩,
        ⟨11234, false, false, [3292], [13, 1]⟩,
        ⟨11228, false, false, [3292], [13, 1]⟩,
        ⟨11228, false, false, [3292], [13, 1]⟩,
        ⟨6051, false, false, [3292, 2827], [1]⟩,
        ⟨6048, false, false, [3292, 2827], []⟩,
        ⟨11392, false, false, [3292, 2827], []⟩,
        ⟨12221, true, false, [3292], [78097]⟩,
        ⟨11396, false, false, [3292, 3333], []⟩,
        ⟨12191, true, false, [], [3333, 78097]⟩,
        ⟨12222, true, false, [], [78097]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 191. -/
def y322TCContextRaw191 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[3337], [3334], .source 1733⟩,
    ⟨[3301, 79333], [3301, 79333], .contexts []⟩,
    ⟨[79333, 15], [3301, 79333], .contexts [
        ⟨12193, false, false, [], []⟩,
        ⟨12193, false, false, [], []⟩,
        ⟨12192, false, false, [3296], [79333, 15]⟩,
        ⟨12149, true, false, [3296, 2865], [15]⟩,
        ⟨11180, true, false, [3296], [3, 15]⟩,
        ⟨11180, true, false, [3296], [3, 15]⟩,
        ⟨11181, true, false, [3296], [3, 15]⟩,
        ⟨4997, true, false, [3296], [3, 15]⟩,
        ⟨1893, false, false, [3296, 77881], []⟩,
        ⟨12187, false, false, [3296], []⟩,
        ⟨12186, false, false, [3296], []⟩,
        ⟨12182, false, false, [3296, 3259], []⟩,
        ⟨12194, true, false, [], [3259, 79333]⟩,
        ⟨12195, true, false, [], [79333]⟩,
        ⟨12225, false, false, [], []⟩,
        ⟨12225, false, false, [], []⟩
      ]⟩,
    ⟨[3301, 79329], [3301, 79329], .contexts []⟩,
    ⟨[3301, 79329], [3301, 79329], .contexts []⟩,
    ⟨[3339], [3300], .source 1734⟩,
    ⟨[3300], [3300], .contexts []⟩,
    ⟨[79331], [3301, 79329], .contexts [
        ⟨12216, true, false, [], []⟩,
        ⟨12229, false, false, [3338], [79333, 1]⟩,
        ⟨12230, false, false, [3338], [79333, 1]⟩,
        ⟨12230, false, false, [3338], [79333, 1]⟩,
        ⟨12182, true, false, [3338, 3300], [1]⟩,
        ⟨911, true, false, [3338, 3300, 79333], [1]⟩,
        ⟨12226, false, false, [3338, 3300], [1, 15, 1, 1]⟩,
        ⟨11958, false, false, [3338], [15, 1, 1]⟩,
        ⟨11955, false, false, [3338], [1, 1]⟩,
        ⟨12227, false, false, [3338, 3300], [1, 1]⟩,
        ⟨12228, false, false, [3338, 3300], [1, 1]⟩,
        ⟨18, false, false, [3338, 79329], []⟩,
        ⟨12229, false, true, [], [79329]⟩
      ]⟩,
    ⟨[79331], [3301, 79329], .contexts [
        ⟨12231, false, false, [], []⟩,
        ⟨12227, false, false, [], []⟩
      ]⟩,
    ⟨[3341], [3339, 3317], .source 1735⟩,
    ⟨[79329, 3], [3341, 78225], .contexts [
        ⟨12232, true, false, [3300], [3]⟩,
        ⟨12202, true, false, [3300, 3314], [3]⟩,
        ⟨35, false, false, [3300, 3314, 78225], []⟩,
        ⟨12203, true, false, [3300], [78225]⟩,
        ⟨12229, true, false, [], [3317, 78225]⟩,
        ⟨12233, true, false, [], [78225]⟩
      ]⟩,
    ⟨[79331], [3301, 79329], .contexts [
        ⟨12232, false, false, [], []⟩,
        ⟨12228, false, false, [], []⟩
      ]⟩,
    ⟨[3343], [3339, 3331], .source 1736⟩,
    ⟨[3345], [3343, 3301], .source 1737⟩,
    ⟨[3347], [3339, 3335], .source 1738⟩,
    ⟨[79327], [3347, 78097], .contexts [
        ⟨11952, true, false, [], []⟩,
        ⟨12235, true, false, [3300], [13]⟩,
        ⟨12223, false, false, [3300], []⟩,
        ⟨12229, true, false, [], [3335, 78097]⟩,
        ⟨12238, true, false, [], [78097]⟩
      ]⟩,
    ⟨[3349], [3347, 1383], .source 1739⟩,
    ⟨[3351], [3348], .source 1740⟩,
    ⟨[3353], [3349, 1369], .source 1741⟩,
    ⟨[3355], [3352], .source 1742⟩,
    ⟨[3355], [3352], .contexts [
        ⟨12243, false, false, [], []⟩
      ]⟩,
    ⟨[78101], [3355, 79323], .contexts [
        ⟨12242, false, false, [3352], [78101]⟩,
        ⟨6206, true, false, [3352, 3349], []⟩,
        ⟨12241, true, true, [3352], [78101, 11]⟩,
        ⟨12240, false, false, [3352, 3350, 3348], [78101, 11]⟩,
        ⟨6211, true, false, [3352, 3350, 3348, 3347], [11]⟩,
        ⟨12239, true, false, [3352, 3350, 3348], [1, 11]⟩,
        ⟨11949, false, false, [3352, 3350, 3348], [11]⟩,
        ⟨12008, false, false, [3352, 3350, 3348], [11]⟩,
        ⟨24, true, false, [3352, 3350, 3348], [79325, 11]⟩,
        ⟨12241, true, false, [3352, 3350], [79325, 11]⟩,
        ⟨11946, false, false, [3352], []⟩,
        ⟨12009, false, false, [3352], []⟩,
        ⟨24, true, false, [3352], [79323]⟩,
        ⟨12244, true, false, [], [79323]⟩
      ]⟩,
    ⟨[3352], [3352], .contexts []⟩,
    ⟨[78101, 9], [3355, 79321], .contexts [
        ⟨12243, true, true, [3352], [78101, 9]⟩,
        ⟨12245, false, false, [3352, 3354], [9]⟩,
        ⟨11943, false, false, [3352], []⟩,
        ⟨12010, false, false, [3352], []⟩,
        ⟨12246, true, false, [], [79321]⟩,
        ⟨12246, true, false, [], [79321]⟩,
        ⟨12244, true, false, [], [79321]⟩
      ]⟩,
    ⟨[3363], [3315, 3301], .source 1746⟩,
    ⟨[78225, 3], [3363, 79329], .contexts [
        ⟨12198, false, false, [], []⟩,
        ⟨12202, false, false, [], []⟩,
        ⟨12235, false, false, [3315], []⟩,
        ⟨12248, true, false, [], [79329]⟩
      ]⟩,
    ⟨[3365], [3363, 3345], .source 1747⟩,
    ⟨[78225, 3, 5, 3], [3365, 3341, 78225], .contexts [
        ⟨12249, false, false, [], [5, 3]⟩,
        ⟨12232, true, false, [3363, 3300], [5, 3]⟩,
        ⟨12215, true, false, [3363, 3300, 3290], [5, 3]⟩,
        ⟨1509, false, false, [3363, 3300, 3290, 79333], [3]⟩,
        ⟨19, false, false, [3363, 3300, 3290, 79333], [3]⟩,
        ⟨12216, false, false, [3363, 3300, 3290], [3]⟩,
        ⟨12199, false, false, [3363, 3300, 3290], [3]⟩,
        ⟨12218, true, false, [3363, 3300], [79331, 3]⟩,
        ⟨12218, true, false, [3363, 3300], [79331, 3]⟩,
        ⟨12217, true, false, [3363, 3300], [79331, 3]⟩,
        ⟨12235, false, false, [3363, 3300, 3331], [3]⟩,
        ⟨12229, true, false, [3363], [3331, 3301, 79329, 3]⟩,
        ⟨12236, true, false, [3363], [3301, 79329, 3]⟩,
        ⟨12237, true, false, [3363], [79329, 3]⟩,
        ⟨12250, true, false, [], [79329, 3]⟩,
        ⟨12234, false, false, [3365], []⟩
      ]⟩,
    ⟨[3367], [3365, 3341], .source 1748⟩,
    ⟨[3369], [3367, 2941], .source 1749⟩,
    ⟨[2941, 77891], [2941, 77891], .contexts []⟩,
    ⟨[2941, 77891], [2941, 77891], .contexts []⟩,
    ⟨[77891, 3], [77891, 3], .contexts []⟩,
    ⟨[3371], [3368], .source 1750⟩,
    ⟨[3373], [3371, 2941], .source 1751⟩,
    ⟨[3375], [3363, 3347], .source 1752⟩,
    ⟨[3043, 78219], [3043, 78219], .contexts []⟩,
    ⟨[78097, 3], [78097, 3], .contexts []⟩,
    ⟨[3377], [3374], .source 1753⟩,
    ⟨[3379], [3377, 3043], .source 1754⟩,
    ⟨[78097, 3], [3379, 78219], .contexts [
        ⟨12261, false, false, [], []⟩,
        ⟨12259, false, false, [3374], [78097, 3]⟩,
        ⟨12239, true, false, [3374, 3363], [3]⟩,
        ⟨11952, true, false, [3374, 3363], [3]⟩,
        ⟨12249, true, false, [3374], [13, 3]⟩,
        ⟨932, false, false, [3374, 78225], []⟩,
        ⟨108, false, false, [3374, 78225], []⟩,
        ⟨11306, false, false, [3374], []⟩,
        ⟨11409, false, false, [3374], []⟩,
        ⟨12260, false, false, [3374], []⟩,
        ⟨12260, false, false, [3374], []⟩,
        ⟨12262, true, false, [], [3043, 78219]⟩,
        ⟨12263, true, false, [], [78219]⟩
      ]⟩,
    ⟨[3381], [3378], .source 1755⟩,
    ⟨[78093], [3067, 78091], .contexts [
        ⟨6038, true, false, [], []⟩,
        ⟨6038, true, false, [], []⟩,
        ⟨6094, true, false, [], []⟩,
        ⟨6093, true, false, [], []⟩,
        ⟨11480, false, false, [3022], [78095, 1]⟩,
        ⟨11481, false, false, [3022], [78095, 1]⟩,
        ⟨11481, false, false, [3022], [78095, 1]⟩,
        ⟨11452, true, false, [3022, 3066], [1]⟩,
        ⟨1485, true, false, [3022, 3066, 78095], [1]⟩,
        ⟨11478, false, false, [3022, 3066], [1, 1]⟩,
        ⟨11479, false, false, [3022, 3066], [1, 1]⟩,
        ⟨18, false, false, [3022, 78091], []⟩,
        ⟨11453, true, false, [], [78091]⟩,
        ⟨11477, false, false, [], []⟩,
        ⟨11454, true, false, [], [78091]⟩,
        ⟨11479, false, false, [], []⟩
      ]⟩,
    ⟨[3385], [1383, 3355], .source 1757⟩,
    ⟨[78091, 9], [78091, 9], .contexts []⟩,
    ⟨[3387], [3023, 3385], .source 1758⟩,
    ⟨[3389], [3386], .source 1759⟩,
    ⟨[3379, 78219], [3379, 78219], .contexts []⟩,
    ⟨[3379, 78217], [3379, 78217], .contexts []⟩,
    ⟨[3379], [3379], .contexts []⟩,
    ⟨[3379], [3379], .contexts []⟩,
    ⟨[3373, 77891], [3373, 77891], .contexts []⟩,
    ⟨[77891, 3, 9], [3373, 77893], .contexts [
        ⟨12256, false, false, [], [9]⟩,
        ⟨12256, false, false, [], [9]⟩,
        ⟨12253, false, false, [3368], [77891, 3, 9]⟩,
        ⟨11294, true, false, [3368, 3367], [3, 9]⟩,
        ⟨12252, false, false, [3368], [78225, 5, 3, 9]⟩,
        ⟨12251, true, false, [3368], [5, 3, 9]⟩,
        ⟨1931, false, false, [3368, 78225], [9]⟩,
        ⟨50, false, false, [3368, 78225], [9]⟩,
        ⟨11294, false, false, [3368], [9]⟩,
        ⟨12254, false, false, [3368], [9]⟩,
        ⟨12255, false, false, [3368], [9]⟩,
        ⟨12255, false, false, [3368], [9]⟩,
        ⟨12257, true, false, [], [2941, 77891, 9]⟩,
        ⟨12258, true, false, [], [77891, 9]⟩,
        ⟨12275, false, false, [], [9]⟩,
        ⟨12275, false, false, [], [9]⟩,
        ⟨5014, false, false, [3373], []⟩
      ]⟩,
    ⟨[3403], [3372], .source 1766⟩,
    ⟨[3372], [3372], .contexts []⟩,
    ⟨[3387, 79319], [3387, 79319], .contexts []⟩,
    ⟨[78091, 9], [3387, 79319], .contexts [
        ⟨12268, false, false, [], []⟩,
        ⟨12268, false, false, [], []⟩,
        ⟨11479, true, false, [3066], [9]⟩,
        ⟨11479, true, false, [3066], [9]⟩,
        ⟨12266, true, false, [3066], [9]⟩,
        ⟨6093, true, false, [3066], [9]⟩,
        ⟨11449, true, false, [3066], [1, 9]⟩,
        ⟨3326, false, false, [3066, 78097], []⟩,
        ⟨1145, false, false, [3066, 78097], []⟩,
        ⟨6210, false, false, [3066], [9, 1]⟩,
        ⟨6211, false, false, [3066], [9, 1]⟩,
        ⟨6199, false, false, [3066], [9, 1]⟩,
        ⟨6200, false, false, [3066], [9, 1]⟩,
        ⟨6200, false, false, [3066], [9, 1]⟩,
        ⟨12247, false, false, [3066, 1383], [1]⟩,
        ⟨12267, true, false, [3066], [79321, 1]⟩,
        ⟨11940, false, false, [3066, 3385], []⟩,
        ⟨11480, true, false, [], [3385, 79319]⟩,
        ⟨12269, true, false, [], [79319]⟩,
        ⟨12279, false, false, [], []⟩
      ]⟩,
    ⟨[78091, 9], [3387, 79319], .contexts [
        ⟨12280, false, false, [], []⟩,
        ⟨12279, false, false, [], []⟩
      ]⟩,
    ⟨[3405], [3389, 3067], .source 1767⟩,
    ⟨[79317, 9], [3405, 78091], .contexts [
        ⟨11937, true, false, [], [9]⟩,
        ⟨12281, true, false, [3386], [5, 9]⟩,
        ⟨1034, false, false, [3386, 78091], []⟩,
        ⟨50, false, false, [3386, 78091], []⟩,
        ⟨6034, false, false, [3386], []⟩,
        ⟨12266, false, false, [3386], []⟩,
        ⟨11479, false, false, [3386], []⟩,
        ⟨11479, false, false, [3386], []⟩,
        ⟨12270, true, false, [], [3067, 78091]⟩,
        ⟨12282, true, false, [], [78091]⟩
      ]⟩,
    ⟨[3407], [3404], .source 1768⟩,
    ⟨[3409], [3389, 3407], .source 1769⟩,
    ⟨[79355], [77147, 7], .source 39742⟩,
    ⟨[77147, 7], [79355], .contexts [
        ⟨12286, true, false, [], []⟩
      ]⟩]

/-- Literal contextual derivation data in chronological chunk 02. -/
def y322TCContextRawChunk02 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCContextRaw128 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw129 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCContextRaw130 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw131 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCContextRaw132 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw133 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCContextRaw134 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw135 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCContextRaw136 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw137 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCContextRaw138 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw139 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCContextRaw140 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw141 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCContextRaw142 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw143 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCContextRaw144 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw145 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCContextRaw146 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw147 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCContextRaw148 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw149 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCContextRaw150 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw151 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCContextRaw152 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw153 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCContextRaw154 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw155 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCContextRaw156 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw157 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCContextRaw158 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw159 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCContextRaw160 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw161 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCContextRaw162 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw163 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCContextRaw164 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw165 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCContextRaw166 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw167 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCContextRaw168 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw169 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCContextRaw170 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw171 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCContextRaw172 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw173 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCContextRaw174 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw175 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCContextRaw176 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw177 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCContextRaw178 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw179 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCContextRaw180 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw181 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCContextRaw182 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw183 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCContextRaw184 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw185 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCContextRaw186 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw187 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCContextRaw188 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw189 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCContextRaw190 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw191 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
