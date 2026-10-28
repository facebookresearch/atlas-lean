/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthBalancedIndexTree
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortData

/-! Exact balanced access to every original source array entry and all absent indices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- All 4136 source entries in their original order, including zero values. -/
def generatedTenthRootTwoRowDescriptorIndexTree : GeneratedNinthBalancedIndexTree :=
  (.branch 2068 (.branch 1034 (.branch 517 (.branch 258 (.branch 129 (.branch 64 (.branch 32
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x27a363d47af600000) (.leaf
  0x274193e875f500000)) (.branch 1 (.leaf 0x2043700200d700000) (.leaf 0x30db88f3b3e40f000)))
  (.branch 2 (.branch 1 (.leaf 0x32fae8f24a808f000) (.leaf 0x10dd38cdb3f04f000)) (.branch 1
  (.leaf 0x327cd8f24540cf000) (.leaf 0x8ada06d9cf40e000)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x22ada3a21c002e000) (.leaf 0x36dd48cdf3f01e000)) (.branch 1 (.leaf
  0x37b27b3c7cd03e000) (.leaf 0xf3ee9ffa2a40d000))) (.branch 2 (.branch 1 (.leaf
  0xf2979e5a1c2ad000) (.leaf 0x9c35289b8415d000)) (.branch 1 (.leaf 0x29ada2adb4f3fd000)
  (.leaf 0x2f3479e622340b000))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2f24f9c02191eb000) (.leaf 0x29a75145b4839b000)) (.branch 1 (.leaf 0x9cda15db8f27b000)
  (.leaf 0x2f06e8b9a05407000))) (.branch 2 (.branch 1 (.leaf 0xf087b4a206367000) (.leaf
  0xa3d83cc4302d7000)) (.branch 1 (.leaf 0xaff7001cce1b7000) (.leaf 0x220dd03c0f0300000))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x279a03d67a2100000) (.leaf 0x12d80b27c9120f000))
  (.branch 1 (.leaf 0x30896b2630768f000) (.leaf 0x32d72b19c9064f000))) (.branch 2 (.branch 1
  (.leaf 0x31f7ab263fb6cf000) (.leaf 0x2b9923b9e6020e000)) (.branch 1 (.leaf
  0x2615207666f62e000) (.leaf 0xcd72b1989061e000)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x2c9228e806263e000) (.leaf 0x1446aa2bd8520d000)) (.branch 1
  (.leaf 0x148c3a31db34ad000) (.leaf 0x2a31215dc2b75d000))) (.branch 2 (.branch 1 (.leaf
  0xb1a2179ce05fd000) (.leaf 0x3451fa3258c20b000)) (.branch 1 (.leaf 0x14902a145b67eb000)
  (.leaf 0x2b1ce291ce759b000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2a292289c2047b000)
  (.leaf 0x147e6b6ddaa207000)) (.branch 1 (.leaf 0x347ca89e5a9567000) (.leaf
  0x9dcc01839f4d7000))) (.branch 2 (.branch 1 (.leaf 0x9b0f3d5b617b7000) (.leaf
  0x2732f3ea752200000)) (.branch 1 (.leaf 0x12900b1bc6110f000) (.leaf 0x31f19b1a3f758f000)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x328f1b25c6054f000) (.leaf
  0x308f5b1a30b5cf000)) (.branch 1 (.leaf 0x2ba3d385e9010e000) (.leaf 0x264fd04a69f52e000)))
  (.branch 2 (.branch 1 (.leaf 0xc8f1b2586051e000) (.leaf 0x2cda18d409253e000)) (.branch 1
  (.leaf 0x142f6a17d7510d000) (.leaf 0x33e39a0dd437ad000)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xb0fd161cdb45d000) (.leaf 0xa13b145c106fd000)) (.branch 1 (.leaf
  0x14391a0e57c10b000) (.leaf 0x13e89a285464eb000))) (.branch 2 (.branch 1 (.leaf
  0xa19d2adc1769b000) (.leaf 0x2b03d2b5cd077b000)) (.branch 1 (.leaf 0x34066b51d5a107000)
  (.leaf 0x140498a2559667000))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x9bcc02436f7d7000) (.leaf 0x9d0f3e9b914b7000)) (.branch 1 (.leaf
  0x30cb08f1b3330f000) (.leaf 0x12f6c8f04a578f000))) (.branch 2 (.branch 1 (.leaf
  0x10c9b8cfb3274f000) (.leaf 0x1284c8f04597cf000)) (.branch 1 (.leaf 0x89f606f9c230e000)
  (.leaf 0x2b763a01cd72e000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x36ca48cff3271e000)
  (.leaf 0x179f4b3e7c073e000)) (.branch 1 (.leaf 0xf3a69fda2730d000) (.leaf
  0x2f18c9e7a115ad000))) (.branch 2 (.branch 1 (.leaf 0x29c9928bb8965d000) (.leaf
  0x299f62afb424fd000)) (.branch 1 (.leaf 0x2f44f9e422e30b000) (.leaf 0xf1d49c22146eb000)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x9a59147b4549b000) (.leaf
  0x9bf615fb8257b000)) (.branch 1 (.leaf 0xf0b48bba08307000) (.leaf 0xf0fdb4820b467000)))
  (.branch 2 (.branch 1 (.leaf 0x2a46e3ce43d5d7000) (.leaf 0xaf61003cc36b7000)) (.branch 1
  (.leaf 0xbe60001f96480000) (.leaf 0x80c803e001440000)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xbd6f001f6a4c0000) (.leaf 0x1068189e2f1001000)) (.branch 1 (.leaf
  0x107b8b51afe421000) (.leaf 0x29ff903e401411000))) (.branch 2 (.branch 1 (.leaf
  0x2b3223cfcf3431000) (.leaf 0x833c10c114002000)) (.branch 1 (.leaf 0x2843c1161226a2000)
  (.leaf 0x2d168a7a0ba552000)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xca95a5e0717f2000) (.leaf 0x283cf11591d004000)) (.branch 1 (.leaf
  0x84cf1339275e4000) (.leaf 0xcb0c9b6076794000))) (.branch 2 (.branch 1 (.leaf
  0x2d0929ae0b1674000) (.leaf 0x85b804a13b008000)) (.branch 1 (.leaf 0x85843b9938768000)
  (.leaf 0x36943b3ff0e6d8000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x37e708f27f05b8000)
  (.leaf 0x2789f03ff970c0000)) (.branch 1 (.leaf 0x225e0000fc040000) (.leaf
  0x3419689fd67481000))) (.branch 2 (.branch 1 (.leaf 0x141aab505680a1000) (.leaf
  0x3e1003fb97091000)) (.branch 1 (.leaf 0x3c133ce3650b1000) (.leaf 0x62f110de82482000)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x26726117eb4222000) (.leaf
  0x36c0ea7bf2c1d2000)) (.branch 1 (.leaf 0x37d96a5ffe7372000) (.leaf 0x638611468b484000)))
  (.branch 2 (.branch 1 (.leaf 0x266961326b1164000) (.leaf 0x17cfc9b7fe0314000)) (.branch 1
  (.leaf 0x16ba29aff272f4000) (.leaf 0x2662604bead488000)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x66523b86ae3e8000) (.leaf 0x2ce33b3e098258000)) (.branch 1 (.leaf
  0x2c9808f3866138000) (.leaf 0x274f003ff6b080000))) (.branch 2 (.branch 1 (.leaf
  0x1066b8a02f0441000) (.leaf 0x307d2b6faff061000)) (.branch 1 (.leaf 0x240a8000400051000)
  (.branch 1 (.leaf 0x44a73f1cf2071000) (.leaf 0x23ff132115442000))))))))) (.branch 64
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x224ff1281232e2000) (.leaf 0x2d180a440bb112000)) (.branch 1 (.leaf 0xca7da600703b2000)
  (.leaf 0x248c12b91c444000))) (.branch 2 (.branch 1 (.leaf 0x2258c10d9261a4000) (.leaf
  0xcb249880773d4000)) (.branch 1 (.leaf 0x2d07a9900b0234000) (.leaf 0x267b07413a448000))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x22647387939328000) (.leaf 0x16953b01f0f298000))
  (.branch 1 (.leaf 0x37e838cc7f11f8000) (.leaf 0x3467589fd9b4c1000))) (.branch 2 (.branch 1
  (.leaf 0x145cab505940e1000) (.leaf 0x3c5003fb6b0d1000)) (.branch 1 (.leaf
  0x3e533ce3990f1000) (.leaf 0x627910de7e4c2000))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x25e2d117e48262000) (.leaf 0x37b78a7bfd0192000)) (.branch 1 (.leaf
  0x36a85a5ff1b332000) (.leaf 0x621e1146774c4000))) (.branch 2 (.branch 1 (.leaf
  0x25ed913264d124000) (.leaf 0x16a8d9b7f1c354000)) (.branch 1 (.leaf 0x17c759affdb2b4000)
  (.leaf 0x25ee904be514c8000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x5f3d3b86523a8000)
  (.leaf 0x2c953b3e064218000)) (.branch 1 (.leaf 0x2ce608f389a178000) (.leaf
  0x81ce3cf80f420000))) (.branch 2 (.branch 1 (.leaf 0x366698a06f0410000) (.leaf
  0x35019b51e02430000)) (.branch 1 (.leaf 0x11d769923e5003000) (.leaf
  0x11bc39883d36a3000)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x231412e424b553000) (.leaf 0x232d22c02807f3000)) (.branch 1 (.leaf 0x31e1f98bbec005000)
  (.leaf 0x31c099adbd65e5000))) (.branch 2 (.branch 1 (.leaf 0x23301128287795000) (.leaf
  0x230bd130240675000)) (.branch 1 (.leaf 0x31ae68d43ca009000) (.leaf 0x31acdb27bc9769000))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2587a3a1dff6d9000) (.leaf 0x244cf06c5015b9000))
  (.branch 1 (.leaf 0x167d4b6feff030000) (.leaf 0x3512789e60d010000))) (.branch 2 (.branch 1
  (.leaf 0x11deea5dbea423000) (.leaf 0x11c9ba47bdc283000)) (.branch 1 (.leaf
  0x904112ba44173000) (.leaf 0x292d210fa8f3d3000))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x31d47a443e3425000) (.leaf 0x31c51a623d91c5000)) (.branch 1 (.leaf
  0x92812e7a883b5000) (.leaf 0x290bd2ffa4f255000))) (.branch 2 (.branch 1 (.leaf
  0x31a6eb1bbc5429000) (.leaf 0x31a858e83c6349000)) (.branch 1 (.leaf 0xb7ba06e5f02f9000)
  (.leaf 0x2b4153a3d0e199000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x220f23f18f2020000)
  (.leaf 0x24628132515413000)) (.branch 1 (.leaf 0x47281285232b3000) (.leaf
  0x13174a444bb143000))) (.branch 2 (.branch 1 (.leaf 0x32a7da604703e3000) (.leaf
  0x246d712bd1c415000)) (.branch 1 (.leaf 0x47b810dd261f5000) (.leaf
  0x32b14988477385000))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x1307a9904b0265000) (.leaf 0x2492807453a419000)) (.branch 1 (.leaf
  0x48fc387d39379000) (.leaf 0x30954b01b0f2c9000))) (.branch 2 (.branch 1 (.leaf
  0x11e888cc3f11a9000) (.leaf 0x256ac2c3de7433000)) (.branch 1 (.leaf 0x55232d9dd1293000)
  (.leaf 0x326d09b5c49163000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x32c1f991c823c3000)
  (.leaf 0x57372da5ee435000)) (.branch 1 (.leaf 0x255772fc5d41d5000) (.leaf
  0x12c74a79c853a5000))) (.branch 2 (.branch 1 (.leaf 0x1261fa61c42245000) (.leaf
  0x25467385dc8439000)) (.branch 1 (.leaf 0x254930765cb359000) (.leaf 0x31fab8f03fd2e9000)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x10837b3db03189000) (.leaf
  0x9a201a0366a0000)) (.branch 1 (.leaf 0xe84eb761ae550000) (.leaf 0xe176b521657f0000)))
  (.branch 2 (.branch 1 (.leaf 0x32d019809006000) (.leaf 0x8f103f8335e6000)) (.branch 1 (.leaf
  0x2e12c8ba162796000) (.leaf 0x2e7768a21a5676000)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x88314602f00a000) (.leaf 0x8402b582c76a000)) (.branch 1 (.leaf 0x1526ea33e1a6da000) (.leaf
  0x165509fe6e45ba000))) (.branch 2 (.branch 1 (.leaf 0xe638b6c1983f0000) (.leaf
  0xdfc5b48153150000)) (.branch 1 (.leaf 0x20a6d00383f6a6000) (.leaf 0x26b025805346000))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xdfdc8a0154136000) (.leaf
  0x2e5c38b81930d6000)) (.branch 1 (.leaf 0x5e015c0196aa000) (.leaf 0x206232af81a1ca000)))
  (.branch 2 (.branch 1 (.leaf 0x3541ba29e2c07a000) (.leaf 0x163a09e46d231a000)) (.branch 1
  (.leaf 0x1bfe0240cb2a0000) (.leaf 0x2e7a7b6f9a7556000)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xe6b1b4999d0b6000) (.leaf 0x21c523cc0cc2c6000)) (.branch 1 (.leaf 0x3c23d400b326000)
  (.leaf 0x2e410a3018155a000))) (.branch 2 (.branch 1 (.leaf 0x2e4289c398223a000) (.leaf
  0x7afc145fb438a000)) (.branch 1 (.leaf 0x728f28874a0ea000) (.leaf 0x2e21db4b96c7f6000)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e00db6d956216000) (.leaf
  0x3243e8007066000)) (.branch 1 (.leaf 0x1ace3f00c0186000) (.leaf 0x2dee6a1414a7fa000)))
  (.branch 2 (.branch 1 (.leaf 0x2decd9e794909a000) (.leaf 0x767a161f7f12a000)) (.branch 1
  (.leaf 0x76d32ac78124a000) (.leaf 0xa1e02603a5e0000)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2e2078a396b790000) (.leaf 0xe81f8bb9ac670000)) (.branch 1 (.leaf 0x78c15f82600c000)
  (.leaf 0x2074f2ac02576c000))) (.branch 2 (.branch 1 (.leaf 0x151bba2a6136dc000) (.leaf
  0x166379e7eed5bc000)) (.branch 1 (.leaf 0x2df94885951270000) (.branch 1 (.leaf
  0xe60a89d996390000) (.leaf 0x2063017981c5ec000)))))))))) (.branch 129 (.branch 64 (.branch
  32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2067328a01f28c000)
  (.leaf 0x353cba0c62933c000)) (.branch 1 (.leaf 0x164219c1ed705c000) (.leaf
  0x1b820180c71e0000))) (.branch 2 (.branch 1 (.leaf 0xdf2e9fc14d79c000) (.leaf
  0xdf45a0f94e0fc000)) (.branch 1 (.leaf 0x2764c289f7814c000) (.leaf 0x2770f14478622c000))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e4ea9e418a67c000) (.leaf 0x2e4d2a1798911c000))
  (.branch 1 (.leaf 0x27b7a291fbf0ac000) (.leaf 0x271d315c7413cc000))) (.branch 2 (.branch 1
  (.leaf 0x202573f3803760000) (.leaf 0x354eeb75e356d0000)) (.branch 1 (.leaf
  0x162fe8b86cb5b0000) (.leaf 0x155038866361b0000))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x162b0b4bec82d0000) (.leaf 0x22713cd8fe360000)) (.branch 1 (.leaf
  0xaca00ebca0600800) (.leaf 0xa62f0d7c50500800))) (.branch 2 (.branch 1 (.leaf
  0x960233db02700800) (.leaf 0xc48fbcc03140f800)) (.branch 1 (.leaf 0x3779fbcdfa708f800)
  (.leaf 0xc477bf203004f800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3707fbcdf5b0cf800)
  (.leaf 0x234da3522c040e800)) (.branch 1 (.leaf 0x94da09dacf02e800) (.leaf
  0x32477bf243001e800))) (.branch 2 (.branch 1 (.leaf 0x13227803cc203e800) (.leaf
  0xdb6fac012540d800)) (.branch 1 (.leaf 0xd9c3ada1132ad800) (.leaf 0x214041b608b15d800))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x20acb1920403fd800) (.leaf
  0x2dc17ad992c40b800)) (.branch 1 (.leaf 0x2da09aff9161eb800) (.leaf 0xb8427a04739b800)))
  (.branch 2 (.branch 1 (.leaf 0x12c426208027b800) (.leaf 0xd8e7b8610a407800)) (.branch 1
  (.leaf 0x2d8cd875909367800) (.leaf 0x716e0f3f3f2d7800)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x27be133e7c11b7800) (.leaf 0x29fdb303bff300800)) (.branch 1 (.leaf
  0x2ad760e9cad100800) (.leaf 0x176c281879e20f800))) (.branch 2 (.branch 1 (.leaf
  0xc0b281980868f800) (.leaf 0x176d382679f64f800)) (.branch 1 (.leaf 0xd6cd8198f46cf800)
  (.leaf 0x24d5208656f20e800))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2b592349d6062e800) (.leaf 0x316d482639f61e800)) (.branch 1 (.leaf 0x31227bd7b6d63e800)
  (.leaf 0x35cee91468a20d800))) (.branch 2 (.branch 1 (.leaf 0x3619290e6bc4ad800) (.leaf
  0x26f9226272475d800)) (.branch 1 (.leaf 0x27f4e2467ef5fd800) (.leaf 0x15c3a90de8320b800))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3615192beb97eb800) (.leaf 0x27f221ae7e859b800))
  (.branch 1 (.leaf 0x70421b672f47b800) (.leaf 0x15f6a8526a5207800))) (.branch 2 (.branch 1
  (.leaf 0x35f85ba1ea6567800) (.leaf 0x214b43278904d7800)) (.branch 1 (.leaf
  0x109b0ea06e7b7800) (.leaf 0x2a7590d5c5d200800))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1724182476e10f800) (.leaf 0xd72e8258f858f800))
  (.branch 1 (.leaf 0x1725381a76f54f800) (.leaf 0xc0518258045cf800))) (.branch 2 (.branch 1
  (.leaf 0x250fd0ba59f10e800) (.leaf 0x2b63d375d9052e800)) (.branch 1 (.leaf
  0x3125481a36f51e800) (.leaf 0x316a7bebb9d53e800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x35b6192867a10d800) (.leaf 0x1571b93264c7ad800)) (.branch 1 (.leaf 0x7d8d25e7d445d800)
  (.leaf 0x26f1d27a71f6fd800))) (.branch 2 (.branch 1 (.leaf 0x35ac7931e7310b800) (.leaf
  0x356c9917e494eb800)) (.branch 1 (.leaf 0x6ebb19271869b800) (.leaf 0x7dfd18a7df77b800)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x357e986e655107800) (.leaf
  0x15805b9de56667800)) (.branch 1 (.leaf 0x20eb431b8607d7800) (.leaf 0x169b0d609e4b7800)))
  (.branch 2 (.branch 1 (.leaf 0x2c594bce03c30f800) (.leaf 0x377debcffaa78f800)) (.branch 1
  (.leaf 0x2c5acbf003d74f800) (.leaf 0x36ffdbcff567cf800)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x35763502cd30e800) (.leaf 0x93f609fac272e800)) (.branch 1 (.leaf
  0x125a4bf043d71e800) (.leaf 0x13357801ccf73e800))) (.branch 2 (.branch 1 (.leaf
  0x2dbb4ac212830d800) (.leaf 0xdacbad811e5ad800)) (.branch 1 (.leaf 0x2133b1b408665d800)
  (.leaf 0xc9419004d4fd800)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xdb0cadb92130b800) (.leaf 0x2da81afd91b6eb800)) (.branch 1 (.leaf 0xbbb27804a49b800)
  (.leaf 0x2147b26008d57b800))) (.branch 2 (.branch 1 (.leaf 0xd89eb84107307800) (.leaf
  0xd854877904467800)) (.branch 1 (.leaf 0x70980f1f325d7800) (.leaf 0x7cb733c7cc6b7800))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2abdf33e499480800) (.leaf 0x296be301b0e440800))
  (.branch 1 (.leaf 0x2a7b033e4654c0800) (.leaf 0xefb8ba19fe001800))) (.branch 2 (.branch 1
  (.leaf 0xee8286e1f1421800) (.leaf 0xbbe8301f0e411800)) (.branch 1 (.leaf
  0x2bfe70f07fc431800) (.leaf 0x28dcf233a1b002800))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x8ee0229a2d6a2800) (.leaf 0x318e0945bb5552800)) (.branch 1 (.leaf
  0x313b8961b7e7f2800) (.leaf 0x8d3c22a212004800))) (.branch 2 (.branch 1 (.leaf
  0x28e6c20c2285e4800) (.leaf 0x11340a89b79794800)) (.branch 1 (.leaf 0x119b8a91bbe674800)
  (.leaf 0x8f84375a34008800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x8fb8086237768800)
  (.leaf 0x120008004016d8800)) (.branch 1 (.leaf 0x337d0bcdcff5b8800) (.leaf
  0x243203004980c0800))) (.branch 2 (.branch 1 (.leaf 0x3feb33fbf3040800) (.leaf
  0x159a9ba0668481800)) (.branch 1 (.leaf 0x3599686fe670a1800) (.branch 1 (.leaf
  0x15a8300098091800) (.leaf 0x210270f186a0b1800))))))))) (.branch 65 (.branch 32 (.branch 16
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x4fc623258d482800) (.leaf
  0x253562285bb222800)) (.branch 1 (.leaf 0x123409444231d2800) (.leaf 0x335bd9604e8372800)))
  (.branch 2 (.branch 1 (.leaf 0x4ef122bd84484800) (.leaf 0x253a620ddbe164800)) (.branch 1
  (.leaf 0x33656a884ef314800) (.leaf 0x123aea904282f4800)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x51923745a2488800) (.leaf 0x25166087da13e8800)) (.branch 1 (.leaf
  0x31616801b97258800) (.leaf 0x111c6bcc369138800))) (.branch 2 (.branch 1 (.leaf
  0x2422f300464080800) (.leaf 0x2efd1b9f9ff441800)) (.branch 1 (.leaf 0xee6b8501f0061800)
  (.leaf 0x26db933ff0f051800))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x280620ce7fd071800) (.leaf 0x2e8c20da1a442800)) (.branch 1 (.leaf 0x22fa3217a2c2e2800)
  (.leaf 0x118cb97bbb4112800))) (.branch 2 (.branch 1 (.leaf 0x113d395fb7f3b2800) (.leaf
  0x2dff214213444800)) (.branch 1 (.leaf 0x22f2f2322291a4800) (.leaf 0x3132bab7b783d4800))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x319d3aafbbf234800) (.leaf 0x2304734ba35448800))
  (.branch 1 (.leaf 0x307b0b8236328800) (.leaf 0x11ff383e400298800))) (.branch 2 (.branch 1
  (.leaf 0x137c0bf3cfe1f8800) (.leaf 0x15dc9ba06944c1800)) (.branch 1 (.leaf
  0x35e7586fe9b0e1800) (.leaf 0xf283000640d1800)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x215a70f18960f1800) (.leaf 0x4d9e2325714c2800)) (.branch 1
  (.leaf 0x24a59228547262800) (.leaf 0x134d59444df192800))) (.branch 2 (.branch 1 (.leaf
  0x321cd960414332800) (.leaf 0x4e3922bd784c4800)) (.branch 1 (.leaf 0x249ed20dd42124800)
  (.leaf 0x321c4a88413354800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x133daa904d42b4800)
  (.leaf 0x4bfd37455e4c8800)) (.branch 1 (.leaf 0x24ba9087d5d3a8800) (.leaf
  0x311f5801b6b218800))) (.branch 2 (.branch 1 (.leaf 0x115e5bcc395178800) (.leaf
  0x36d20f0300420800)) (.branch 1 (.leaf 0x14fd4b9fdff410800) (.leaf 0x3392786e50d430800)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2d5d9aad8ea003800) (.leaf
  0x2d489ab78dc6a3800)) (.branch 1 (.leaf 0x286411db944553800) (.leaf 0x88c21ff98f7f3800)))
  (.branch 2 (.branch 1 (.leaf 0xd531ab40e3005800) (.leaf 0xd441a920d95e5800)) (.branch 1
  (.leaf 0x28891217988795800) (.leaf 0x86cd20f94f675800)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2d261beb8c5009800) (.leaf 0x2d2798180c6769800)) (.branch 1 (.leaf
  0xbbba09e6f06d9800) (.leaf 0x2b815353e0e5b9800))) (.branch 2 (.branch 1 (.leaf
  0x34e6a8505f0030800) (.leaf 0x3381aba1d02010800)) (.branch 1 (.leaf 0x2d5629620e5423800)
  (.branch 1 (.leaf 0x2d3b29780d3283800) (.leaf 0x274121414b173800)))))))) (.branch 32
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x28c22301803d3800) (.leaf
  0xd60a97b8ec425800)) (.branch 1 (.leaf 0xd3fa95d8d61c5800) (.leaf 0x29111d81873b5800)))
  (.branch 2 (.branch 1 (.leaf 0x26cd1c0140255800) (.leaf 0x2d2da8240ca429800)) (.branch 1
  (.leaf 0x2d2c2bd78c9349800) (.leaf 0x26c7a351eff2f9800)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x258cf09c601199800) (.leaf 0x40280ce3fd020800)) (.branch 1 (.leaf
  0x25ad720de1a413800) (.leaf 0x5bf8217e2c2b3800))) (.branch 2 (.branch 1 (.leaf
  0x378d897bfb4143800) (.leaf 0x373d495ff7f3e3800)) (.branch 1 (.leaf 0x259e8214613415800)
  (.leaf 0x5ba82326291f5800))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x1733cab7f78385800) (.leaf 0x179d4aaffbf265800)) (.branch 1 (.leaf 0x5cbc34be35419800)
  (.leaf 0x25ce80b8636379800))) (.branch 2 (.branch 1 (.leaf 0x2bff383e0002c9800) (.leaf
  0x2d7bcbf38fe1a9800)) (.branch 1 (.leaf 0x6af71fc6e8433800) (.leaf 0x269f71e66de293800))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x36e7fa8a746163800) (.leaf 0x17535aae78d3c3800))
  (.branch 1 (.leaf 0x26a2c1e5ee1435800) (.leaf 0x69e31c3edb1d5800))) (.branch 2 (.branch 1
  (.leaf 0x174df94678a3a5800) (.leaf 0x36f3295e74d245800)) (.branch 1 (.leaf
  0x268530ba6c7439800) (.leaf 0x26827349ec4359800)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0xd69fbcf8f22e9800) (.leaf 0xc11080200c189800)) (.branch 1
  (.leaf 0x3a2e325b396a0800) (.leaf 0x2ff10849aa1550800))) (.branch 2 (.branch 1 (.leaf
  0xf9ed86da6a7f0800) (.leaf 0x370d326306006800)) (.branch 1 (.leaf 0x3aa230033c5e6800) (.leaf
  0xfa36b85a6d796800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2ffeab9daaa676800) (.leaf
  0x238ca279b2000a800)) (.branch 1 (.leaf 0x2391618a32376a800) (.leaf 0x139eb90c5156da800)))
  (.branch 2 (.branch 1 (.leaf 0x34e06ac1deb5ba800) (.leaf 0x2fe23853a973f0800)) (.branch 1
  (.leaf 0xf89b877a5c150800) (.leaf 0x239e133c3306a6800))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x375131a30a346800) (.leaf 0x2f883b9fa5b136800)) (.branch 1 (.leaf
  0x2fe9ab87a9c0d6800) (.leaf 0x2387a263b166aa800))) (.branch 2 (.branch 1 (.leaf
  0x38461903151ca800) (.leaf 0x33b3b91652307a800)) (.branch 1 (.leaf 0x34cb3adbddd31a800)
  (.leaf 0x29e5231bbc42a0800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xffb88502a8556800)
  (.leaf 0x2fda88762920b6800)) (.branch 1 (.leaf 0x29e010f3bc32c6800) (.leaf
  0x2963d0ebb04326800))) (.branch 2 (.branch 1 (.leaf 0x2fd4690fa8e55a800) (.leaf
  0x2fd2dafc28d23a800)) (.branch 1 (.leaf 0x2ae7a27a4bb38a800) (.branch 1 (.leaf
  0xa5831b7c450ea800) (.leaf 0x2f9478742637f6800))))))))))) (.branch 258 (.branch 129 (.branch
  64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2f851852259216800) (.leaf 0x296810d7b08066800)) (.branch 1 (.leaf 0x9ed20cfbcf186800)
  (.leaf 0xf67592ba457fa800))) (.branch 2 (.branch 1 (.leaf 0xf68dad824609a800) (.leaf
  0xa8cc25e47012a800)) (.branch 1 (.leaf 0x2ab0f193c8e24a800) (.leaf 0x39ed319b355e0800))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xf95cb9c264790800) (.leaf 0xff42b842a3670800))
  (.branch 1 (.leaf 0x2394526032900c800) (.leaf 0x3979193b2a76c800))) (.branch 2 (.branch 1
  (.leaf 0x13a9f915d1c6dc800) (.leaf 0x34d20ad85e25bc800)) (.branch 1 (.leaf
  0xf8c9bba25e270800) (.leaf 0xfe51ba2299390800))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x38152463135ec800) (.leaf 0x37c91b5b1028c800)) (.branch 1 (.leaf
  0x33b89933d2633c800) (.leaf 0x34c30afe5d805c800))) (.branch 2 (.branch 1 (.leaf
  0x29e81327bc81e0800) (.leaf 0xf62cac3a4279c800)) (.branch 1 (.leaf 0xf6149302410fc800)
  (.leaf 0xa8fa1b647714c800)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2aad327bc8922c800)
  (.leaf 0xfc6eadba8567c800)) (.branch 1 (.leaf 0xfc8592828611c800) (.leaf
  0x2adcc1ae4b00ac800))) (.branch 2 (.branch 1 (.leaf 0xa60f263c4e3cc800) (.leaf
  0x2378e0cc30c760800)) (.branch 1 (.leaf 0x13d6384a53a6d0800) (.leaf
  0x14a50b87dc45b0800)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x33d4dbb9d391b0800) (.leaf 0x14a9d8745c72d0800)) (.branch 1 (.leaf 0x29f180f23f1360800)
  (.leaf 0x32602d0ec41405005))) (.branch 2 (.branch 1 (.leaf 0x34ac2f195c9390805) (.leaf
  0x14a7ccd6dc67b0805)) (.branch 1 (.leaf 0x16e11dfef41025805) (.leaf 0x23a3d7b9339780805))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x22a916911be015805) (.leaf 0x891155e9b1435805))
  (.branch 1 (.leaf 0x209d17490393a0005) (.leaf 0x23f31448bcb7a0805))) (.branch 2 (.branch 1
  (.leaf 0x277256094c035805) (.leaf 0x85f26af143415805)) (.branch 1 (.leaf
  0x21bf24b88cb380005) (.leaf 0x17989dc0fbc425805))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x154cffd76343b0005) (.leaf 0x15571c18e3b790005)) (.branch 1 (.leaf
  0x33199d30cbc005005) (.leaf 0x5b87692e25395805))) (.branch 2 (.branch 1 (.leaf
  0x43637baca2400805) (.leaf 0xada34754ad020805)) (.branch 1 (.leaf 0x24787662d257b5005)
  (.leaf 0xf7aff1aa52010805)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x11c6cd0d3da785005)
  (.leaf 0x11bf4ec2bd53a5005)) (.branch 1 (.leaf 0xdfa9fea952430005) (.leaf
  0xfeffceb2a0030805))) (.branch 2 (.branch 1 (.leaf 0x10bafefcb287a5005) (.leaf
  0x30b94d33327385005)) (.branch 1 (.leaf 0xe6f9c1b1a0410005) (.leaf
  0x255b865cdd83b5005))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x73ec774f5f420005) (.leaf 0x2bd294bb750000005)) (.branch 1 (.leaf
  0x69706aced8795805) (.leaf 0x5b186b4e1f675805))) (.branch 2 (.branch 1 (.leaf
  0x42ec79cc981e0805) (.leaf 0xab6c4534975c0805)) (.branch 1 (.leaf 0x246f8644d1f255005)
  (.leaf 0x2f9baf3ca685f0805)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x31cfad2b3e0265005)
  (.leaf 0x31e62ee4bef645005)) (.branch 1 (.leaf 0x2e1bafcc9681d0005) (.leaf
  0x2fe6cccd29a5d0805))) (.branch 2 (.branch 1 (.leaf 0x3099fedab12245005) (.leaf
  0x10aa4d1531d665005)) (.branch 1 (.leaf 0x2e66cc3d19a1f0005) (.leaf 0x2566767ade2655005)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x74a3752f651c0005) (.leaf
  0x2bda649d76a5e0005)) (.branch 1 (.leaf 0x6a9768aee2275805) (.leaf 0x172dfe177741e5805)))
  (.branch 2 (.branch 1 (.leaf 0x16789c00efc670005) (.leaf 0x366b4fcf6f3250005)) (.branch 1
  (.leaf 0x32ac9ee74745c5005) (.leaf 0x3f04a080c260005)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x3331588a8b5f5005) (.leaf 0x292316472841d5005)) (.branch 1 (.leaf
  0x376d450b0c640805) (.leaf 0x2228d7510fe240005))) (.branch 2 (.branch 1 (.leaf
  0x323d6792795d5005) (.leaf 0x913d5b6a761f5005)) (.branch 1 (.leaf 0x2407d7a13fe660805)
  (.leaf 0x12cd7ed94891c5005)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x13807cced01650805) (.leaf 0x1393af0150e270805)) (.branch 1 (.leaf
  0x374c2e297895e5805) (.leaf 0x2baae6906b040400b))) (.branch 2 (.branch 1 (.leaf
  0x34ac1c19dc939080b) (.leaf 0xf8e5c1825f71080b)) (.branch 1 (.leaf 0x22f4f5ae22908480b)
  (.leaf 0x14ab3c27dc87d080b)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x25369591dbe04480b)
  (.leaf 0x28e8c5902284c480b)) (.branch 1 (.leaf 0x2df92f1995135000b) (.leaf
  0xff44c182a375080b))) (.branch 2 (.branch 1 (.leaf 0x235ff5ae2d50c480b) (.leaf
  0xb5245afd4344480b)) (.branch 1 (.leaf 0x15560f2663a3d000b) (.leaf 0x2953c5902d448480b)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e830f199ad31000b) (.leaf
  0x15572f1863b79000b)) (.branch 1 (.leaf 0x25eb66ae64d00400b) (.leaf 0x133dcd0c4d439480b)))
  (.branch 2 (.branch 1 (.leaf 0x243604ba4a240080b) (.leaf 0x299514bbb3408080b)) (.branch 1
  (.leaf 0x2c72ae3204d71400b) (.leaf 0x2acdf4844a304080b)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x37c64e0dfda7d400b) (.leaf 0x2c711e0c04c35400b)) (.branch 1 (.leaf
  0x9fe7ba03a4c000b) (.leaf 0x29ea14bbbc80c080b))) (.branch 2 (.branch 1 (.leaf
  0x2d094e320b175400b) (.leaf 0x16ba4e33f273d400b)) (.branch 1 (.leaf 0x272f0785f5144000b)
  (.branch 1 (.leaf 0x2d07ce0c0b031400b) (.leaf 0x1b5e7ba0c648000b))))))))) (.branch 64
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xbd2f7bbf5000000b) (.leaf 0x123cfd3242979480b)) (.branch 1 (.leaf 0x33647d2a4ee67480b)
  (.leaf 0x242ef49c4981e080b))) (.branch 2 (.branch 1 (.leaf 0x296de49db0e56080b) (.leaf
  0xcb22e140772f400b)) (.branch 1 (.leaf 0x2abb04a24995a080b) (.leaf 0x17cfae2bfe023400b))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xcb0ae2a0766b400b) (.leaf 0x10679c00012000b))
  (.branch 1 (.leaf 0x29f4e49dbf252080b) (.leaf 0xccf9e1408b2b400b))) (.branch 2 (.branch 1
  (.leaf 0x36aace15f1d63400b) (.leaf 0x2751f7a3f6b1a000b)) (.branch 1 (.leaf
  0xcce2e2a08a6f400b) (.leaf 0x223e79c0fc16000b))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0xbda079df6a5e000b) (.leaf 0x321c2d1441327480b)) (.branch 1 (.leaf
  0x2b621589d851e480b) (.leaf 0x1678af006fc67000b))) (.branch 2 (.branch 1 (.leaf
  0xe1e8f0196a2f000b) (.leaf 0x246c6b791c56400b)) (.branch 1 (.leaf 0x167a8f3e6fd23000b)
  (.leaf 0x639668868b5a400b)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x283af68991d12400b)
  (.leaf 0xf95ac002646b080b)) (.branch 1 (.leaf 0xe60cf019962b000b) (.leaf
  0x2bc06b79e052400b))) (.branch 2 (.branch 1 (.leaf 0xb9ab6b66761a400b) (.leaf
  0x3395bc3fd0f63080b)) (.branch 1 (.leaf 0x28b036899e116400b) (.leaf 0xfe3dc002986f080b))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x13939c01d0e27080b) (.leaf
  0x4e495b7d785e480b)) (.branch 1 (.leaf 0x3065fc522ef2709ba) (.leaf 0x29e1568bbc367b1ba)))
  (.branch 2 (.branch 1 (.leaf 0xa87555fc6c07b1ba) (.leaf 0x35750cb9e4f4701ba)) (.branch 1
  (.leaf 0x2d7b7e780fd2741ba) (.leaf 0x367b79e2de67f1ba)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x4d6f44a57107f1ba) (.leaf 0x128aae93c5d4749ba)) (.branch 1 (.leaf
  0x2d79fe460fc6341ba) (.leaf 0x95b87a02df23f1ba))) (.branch 2 (.branch 1 (.leaf
  0xb5b047457043f1ba) (.leaf 0x32888eadc5c0349ba)) (.branch 1 (.leaf 0xed12f539e16301ba)
  (.leaf 0x21c8f58a0cd23b9ba))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2743565e76243b9ba) (.leaf 0x13e12fb85410309ba)) (.branch 1 (.leaf 0x22d956e620c2751ba)
  (.leaf 0x2c453f0002f67e1ba))) (.branch 2 (.branch 1 (.leaf 0x373f7cd478007e1ba) (.leaf
  0xba8360deac4759ba)) (.branch 1 (.leaf 0x297207f3b112711ba) (.leaf 0xf5a3d2a23d67a9ba))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x145a2efe59207a9ba) (.leaf 0x7a8d7187b14719ba))
  (.branch 1 (.leaf 0x37e37cdb106311ba) (.leaf 0xf589d1423c23a9ba))) (.branch 2 (.branch 1
  (.leaf 0x145b1ec059343a9ba) (.leaf 0xbec87267b00319ba)) (.branch 1 (.leaf
  0x282065e79026359ba) (.leaf 0x30b12c01b2123e9ba))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x12d4afd5c8e43e9ba) (.leaf 0x517750c5a20351ba))
  (.branch 1 (.leaf 0x3214fdb7c0e6451ba) (.leaf 0x2b89e451e2d24e1ba))) (.branch 2 (.branch 1
  (.leaf 0x880678598244e1ba) (.leaf 0x2d038d5c0ae0459ba)) (.branch 1 (.leaf
  0x339b1ca25136411ba) (.leaf 0x417067bc3f24a9ba)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x23db85afb9044a9ba) (.leaf 0x2e8b1c499b30419ba)) (.branch 1 (.leaf 0x339a2c9c5122011ba)
  (.leaf 0x2a4af645c3e60a9ba))) (.branch 2 (.branch 1 (.leaf 0x9cfb591b9100a9ba) (.leaf
  0xe898c779b24019ba)) (.branch 1 (.leaf 0x167ffeb67002059ba) (.leaf 0x475575052360e9ba)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x339548428c00e9ba) (.leaf
  0x116f7e5dba04051ba)) (.branch 1 (.leaf 0x27e7743c7e26401ba) (.leaf 0x3633bee5ece24b9ba)))
  (.branch 2 (.branch 1 (.leaf 0xe107d3196144b9ba) (.leaf 0x29a224d7b420409ba)) (.branch 1
  (.leaf 0xb7c86165f06449ba) (.leaf 0x37bb3ff07d324f9ba)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2cb8fc2407c44f9ba) (.leaf 0x227bc6fd9500441ba)) (.branch 1 (.leaf
  0x578d6285f12049ba) (.leaf 0x37ba2fce7d260f9ba))) (.branch 2 (.branch 1 (.leaf
  0x2cba7c1a07d00f9ba) (.leaf 0x86ff6c39514041ba)) (.branch 1 (.leaf 0xb26f73dcec2009ba)
  (.leaf 0x349f7de45c060b1ba)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2fa57e3026f00b1ba) (.leaf 0xc567d604c4001ba)) (.branch 1 (.leaf
  0x364f7c9d6e06019b4) (.leaf 0x27ce6644fcc20a1b4))) (.branch 2 (.branch 1 (.leaf
  0x20f2559086340a1b4) (.leaf 0xf5eec76a400011b4)) (.branch 1 (.leaf 0x3115feb6b642851b4)
  (.leaf 0x226fa75094768e1b4)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x26afa484ee808e1b4)
  (.leaf 0x37a52e5d7c44859b4)) (.branch 1 (.leaf 0x3163feb6b982c51b4) (.leaf
  0x22a4a7509bb6ce1b4))) (.branch 2 (.branch 1 (.leaf 0x25a32484e140ce1b4) (.leaf
  0x36d2ee5d7384c59b4)) (.branch 1 (.leaf 0x339b2fa2d136411b4) (.leaf 0x2417357b43f24a9b4)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3dbb6af39044a9b4) (.leaf
  0x2e8b2f491b30419b4)) (.branch 1 (.leaf 0x259a65e6e0c2241b4) (.leaf 0x12454c00c2f62f1b4)))
  (.branch 2 (.branch 1 (.leaf 0x113f7fd4b8002f1b4) (.leaf 0x93a550d2ac4249b4)) (.branch 1
  (.leaf 0x138a4f28876a01b4) (.leaf 0xe7f4e2b1ab2ab9b4)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x35052dff6044ab9b4) (.leaf 0x2a2c04194270a09b4)) (.branch 1 (.leaf
  0x11f24f287b6e01b4) (.leaf 0xe014e2b1572eb9b4))) (.branch 2 (.branch 1 (.leaf
  0x3672ddff6f84eb9b4) (.leaf 0x2b10c4194db0e09b4)) (.branch 1 (.leaf 0x588b6d95ff2649b4)
  (.branch 1 (.leaf 0x37c8cf3f7dc66f9b4) (.leaf 0xcab5ceb07306f9b4)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x87bf63295f4641b4) (.leaf 0x2d6c7e890f32141b4)) (.branch 1 (.leaf 0x35bb76f2d061f1b4)
  (.leaf 0x24e734bb57f01f1b4))) (.branch 2 (.branch 1 (.leaf 0x127b6e62c534149b4) (.leaf
  0x15b3af9d6786901b4)) (.branch 1 (.leaf 0x2736a544f5429b9b4) (.leaf 0x221f06908fb49b9b4))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3043af76ad80909b4) (.leaf 0x15c52f9d6846d01b4))
  (.branch 1 (.leaf 0x279fa544fa82db9b4) (.leaf 0x202ec6908074db9b4))) (.branch 2 (.branch 1
  (.leaf 0x2f34ef76a240d09b4) (.leaf 0x307ffdb6b002549b4)) (.branch 1 (.leaf
  0x252645092365f9b4) (.leaf 0x63e6784e8c05f9b4))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x376f7d5d7a04541b4) (.leaf 0x237e04cd3106311b4)) (.branch 1 (.leaf
  0xf58ae14a3c23a9b4) (.leaf 0x145b2dc0d9343a9b4))) (.branch 2 (.branch 1 (.leaf
  0x2bece426fb00319b4) (.leaf 0x64906e6e942b59b4)) (.branch 1 (.leaf 0x13122f00cb76be9b4)
  (.leaf 0x10a3acd4b180be9b4)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x28f7160d2344b51b4)
  (.leaf 0x61006e6e682f59b4)) (.branch 1 (.leaf 0x126faf00c4b6fe9b4) (.leaf
  0x11d4dcd4be40fe9b4))) (.branch 2 (.branch 1 (.leaf 0x2947160d2c84f51b4) (.leaf
  0x1f087f28e36719b4)) (.branch 1 (.leaf 0x2eb5fd2b1cf27a1b4) (.leaf 0x158edeff66047a1b4))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2a5667194430711b4) (.leaf
  0x24e6907bd7f03f1b5)) (.branch 1 (.leaf 0x3091f94a30c1349b5) (.leaf 0x328c4aa045e3349b5)))
  (.branch 2 (.branch 1 (.leaf 0x842a0ae12223f9b5) (.leaf 0x221f32500fb4bb9b5)) (.branch 1
  (.leaf 0x344a285e5875b09b5) (.leaf 0x303f2bb42d57b09b5)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xacf5285ca66bb1b5) (.leaf 0x202f52500074fb9b5)) (.branch 1 (.leaf
  0x3437985e57b5f09b5) (.leaf 0x2f3c5bb42297f09b5))) (.branch 2 (.branch 1 (.leaf
  0xa705285c5a6fb1b5) (.leaf 0x63dc34468c07f9b5)) (.branch 1 (.leaf 0x2d7e7a758ff1741b5)
  (.leaf 0x3782599ffad3741b5))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x29504391ad127f1b5) (.leaf 0x3468eacfd9c03a9b5)) (.branch 1 (.leaf 0x1ed70c18e01319b5)
  (.leaf 0x7aa932bfb23319b5))) (.branch 2 (.branch 1 (.leaf 0x2ea0ca1a1c123a1b5) (.leaf
  0x10a22bdbb174be9b5)) (.branch 1 (.leaf 0x24ccf2ea5645b51b5) (.leaf 0x230a11002367b51b5))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x16eeab0e74a6be1b5) (.leaf 0x11df6bdbbeb4fe9b5))
  (.branch 1 (.leaf 0x250bf2ea5985f51b5) (.leaf 0x235611002ca7f51b5))) (.branch 2 (.branch 1
  (.leaf 0x17901b0e7b66fe1b5) (.leaf 0x35a519f066f07a1b5)) (.branch 1 (.leaf
  0x237f33fe3131711b5) (.leaf 0x241c40144413711b5))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2f499925a3227a9b5) (.leaf 0x23e8419e39e40a9b5))
  (.branch 1 (.leaf 0x36519b906e25019b5) (.leaf 0x2e86987a1b07019b5))) (.branch 2 (.branch 1
  (.leaf 0x2bf1914bfc360a1b5) (.leaf 0x464508a51508e9b5)) (.branch 1 (.leaf
  0x1118f9bbb661851b5) (.leaf 0x124d1a51c343851b5)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x868605f94828e1b5) (.leaf 0x571d08a5e90ce9b5)) (.branch 1 (.leaf 0x1166f9bbb9a1c51b5)
  (.leaf 0x132ada51cc83c51b5))) (.branch 2 (.branch 1 (.leaf 0x895605f9b42ce1b5) (.leaf
  0x210292a186d44a1b5)) (.branch 1 (.leaf 0x1398c8afd115411b5) (.leaf 0xf635b45a437411b5)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2a3a927443064a9b5) (.leaf
  0xca9e81587240f9b5)) (.branch 1 (.leaf 0x58be1246015041b5) (.leaf 0x28132ce1537041b5)))
  (.branch 2 (.branch 1 (.leaf 0x324578c042f60f1b5) (.leaf 0x14f01a3e5f608b1b5)) (.branch 1
  (.leaf 0x13d603008a1801b5) (.leaf 0x7dbf3da7d83801b5)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2e7f7aeb9ab28b9b5) (.leaf 0x138dea3e50a0cb1b5)) (.branch 1 (.leaf
  0x11a20300761c01b5) (.leaf 0x6f833da7243c01b5))) (.branch 2 (.branch 1 (.leaf
  0x2e017aeb9572cb9b5) (.leaf 0x3140cb2a38144f1b5)) (.branch 1 (.leaf 0x57a921bdf25449b5)
  (.leaf 0x33a91f1aa07449b5)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x17c8fbfffdc64f9b5) (.leaf 0x2297a08a98d04e1bb)) (.branch 1 (.leaf
  0x37fcf9bb7fe1459bb) (.leaf 0x2d00ba510ac3459bb))) (.branch 2 (.branch 1 (.leaf
  0x2b73405f5d024e9bb) (.leaf 0x9dc42a0b9f04a9bb)) (.branch 1 (.leaf 0x365398aeee31419bb)
  (.leaf 0x2e883b449b13419bb)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x27c142757c224a1bb)
  (.leaf 0x3e8729eb9e40a9bb)) (.branch 1 (.leaf 0x3651a890ee25019bb) (.leaf
  0x2e86ab7a9b07019bb))) (.branch 2 (.branch 1 (.leaf 0xbf1f24b7c360a1bb) (.leaf
  0x920938b28340e9bb)) (.branch 1 (.leaf 0x1367fabacf05051bb) (.leaf 0x11724950ba27051bb)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x26a0a35eede60e1bb) (.leaf
  0x2e1049f116146b9bb)) (.branch 1 (.leaf 0x2a2003ff41d5609bb) (.leaf 0x29ab201534f7609bb)))
  (.branch 2 (.branch 1 (.leaf 0x13d88924d3c66b1bb) (.leaf 0xcb8c8e487c46f9bb)) (.branch 1
  (.leaf 0x59b61d560f5641bb) (.leaf 0x285323f15d7641bb)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1230983142166f1bb) (.leaf 0xcba48da87d02f9bb)) (.branch 1 (.leaf
  0x2b8071eb60e1241bb) (.leaf 0x2879020115c3241bb))) (.branch 2 (.branch 1 (.leaf
  0x322e880f42022f1bb) (.leaf 0xfa54af0a6f02b1bb)) (.branch 1 (.leaf 0x26df00fef131201bb)
  (.branch 1 (.leaf 0x20b0a3148413201bb) (.leaf 0x154a4a2563222b9bb))))))))) (.branch 65
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x278ea29ef9e45b9bb) (.leaf 0x10524890ae25509bb)) (.branch 1 (.leaf 0x1486bb7adb07509bb)
  (.leaf 0x29e0924b3c365b1bb))) (.branch 2 (.branch 1 (.leaf 0x2ba1f38b68345f9bb) (.leaf
  0x2d67faba8f05541bb)) (.branch 1 (.leaf 0x3771b950fa27541bb) (.leaf 0x368735eade65f1bb))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x63143b568201f9bb) (.leaf 0x2d697a848f11141bb))
  (.branch 1 (.leaf 0x3773996efa33141bb) (.leaf 0x95c4360adf21f1bb))) (.branch 2 (.branch 1
  (.leaf 0xab2a19f49001b1bb) (.leaf 0xee1ab911ec1101bb)) (.branch 1 (.leaf
  0x161ca87b6be3101bb) (.leaf 0x21c8c14a8cd21b9bb))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x32bac8dac7d07e9bb) (.leaf 0x8cc91eb20e1751bb)) (.branch 1 (.leaf
  0xb54920155c3751bb) (.leaf 0xc2e880f02027e1bb))) (.branch 2 (.branch 1 (.leaf
  0x35a52af0e6f07a1bb) (.leaf 0x37f00feb131711bb)) (.branch 1 (.leaf 0x41c7314c413711bb)
  (.leaf 0x2f49aa2523227a9bb)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x35a41acee6e43a1bb)
  (.leaf 0x97330c0b125311bb)) (.branch 1 (.leaf 0xa4f632ac407311bb) (.leaf
  0xf4b0a1b23363a9bb))) (.branch 2 (.branch 1 (.leaf 0x372c2bdb77343e1bb) (.leaf
  0x22ba2ea9005359bb)) (.branch 1 (.leaf 0x5f40100e527359bb) (.leaf 0x30c4ab0eb2e63e9bb))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x222e52b69004359bf) (.leaf
  0x2c1fb8490165de1bf)) (.branch 1 (.leaf 0x1794fb9d7b93de1bf) (.leaf 0x2b68c25d5a02351bf)))
  (.branch 2 (.branch 1 (.leaf 0x989c0bab281d11bf) (.leaf 0x2dc8397a93103a1bf)) (.branch 1
  (.leaf 0x15ec2aaee9e63a1bf) (.leaf 0x77590517887d19bf)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x395f084b295911bf) (.leaf 0x2dc6a94493047a1bf)) (.branch 1 (.leaf
  0x15ed2a90e9f27a1bf) (.leaf 0x2be0806f7893919bf))) (.branch 2 (.branch 1 (.leaf
  0x28ce61b720e0751bf) (.leaf 0x10a3cb48b1819e9bf)) (.branch 1 (.leaf 0x1312489ccb779e9bf)
  (.leaf 0x2665815ceae6759bf))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2ec07beb1d65f01bf) (.leaf 0x29ee522b3cf41b1bf)) (.branch 1 (.leaf 0x2a76a1ff46021b1bf)
  (.leaf 0x142f8b00d763f09bf))) (.branch 2 (.branch 1 (.leaf 0xd691ad88f10141bf) (.leaf
  0x22c040271e71ff9bf)) (.branch 1 (.leaf 0x5e3b3f36487ff9bf) (.leaf 0x1278aa334516149bf))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xd679ae68f04541bf) (.leaf 0x8b470191e65bf9bf))
  (.branch 1 (.leaf 0x2b8f03cd6493bf9bf) (.leaf 0x32768a0d4502549bf))) (.branch 2 (.branch 1
  (.leaf 0x3043c8eaad81b09bf) (.leaf 0x21b1f12a8c105b9bf)) (.branch 1 (.leaf
  0x752a2fef6e65b9bf) (.branch 1 (.leaf 0x15b3c8016787b01bf) (.leaf
  0x26fd8084f295c01bf)))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x13c6b944d3042b1bf) (.leaf 0x2fed4a90a9f22b1bf)) (.branch 1 (.leaf
  0x9c7106f3893c09bf) (.leaf 0xb8081b760e0241bf))) (.branch 2 (.branch 1 (.leaf
  0x36a2bb48f181cf9bf) (.leaf 0x2d11489c8b77cf9bf)) (.branch 1 (.leaf 0x349015caae6249bf)
  (.leaf 0x259d918960f4641bf)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x36a4ab76f1958f9bf)
  (.leaf 0x2d0fc8a28b638f9bf)) (.branch 1 (.leaf 0x93d3162aaf2649bf) (.leaf
  0x2a2d03854271809bf))) (.branch 2 (.branch 1 (.leaf 0x155c7a4563e06b9bf) (.leaf
  0xe58499119166b9bf)) (.branch 1 (.leaf 0x136a36e8877801bf) (.leaf 0x33679ae6cf04051bf)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2b7710195e65ee9bf) (.leaf
  0x90893cd2493ee9bf)) (.branch 1 (.leaf 0xc768a0d0502059bf) (.leaf 0x1642a8eaed81e19bf)))
  (.branch 2 (.branch 1 (.leaf 0x43b012acc100a9bf) (.leaf 0x23c882feb6e60a9bf)) (.branch 1
  (.leaf 0x2fb2a8012787e11bf) (.leaf 0x1644a8d4ed95a19bf)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xaefb114cc044a9bf) (.leaf 0x29bcb2c0b6f24a9bf)) (.branch 1 (.leaf
  0xfb4083f2793a11bf) (.leaf 0x17fc99e77fe0459bf))) (.branch 2 (.branch 1 (.leaf
  0x26b0a318ee81ae1bf) (.leaf 0x226ea0cc9477ae1bf)) (.branch 1 (.leaf 0x310c790cb5e6451bf)
  (.leaf 0x257e6247df24449b1)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1354f8b84e45af1b1) (.leaf 0x10effb6c34b3af1b1)) (.branch 1 (.leaf
  0x287652ac1522441b1) (.leaf 0xc3604a04c5201b1))) (.branch 2 (.branch 1 (.leaf
  0xf7e798a2554cb1b1) (.leaf 0x34f62a5e5fa2cb1b1)) (.branch 1 (.leaf 0xb2a00a1cec3209b1)
  (.leaf 0x18de04a0b05601b1)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xffc798a2a948b1b1)
  (.leaf 0x3387da5e50628b1b1)) (.branch 1 (.leaf 0xa1450a1c103609b1) (.leaf
  0x258d11786014041b1))) (.branch 2 (.branch 1 (.leaf 0x16a17b87f175ef9b1) (.leaf
  0x2d12d8538b83ef9b1)) (.branch 1 (.leaf 0x9313193aa12049b1) (.leaf 0x33bff8d5d2b1a11b1)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x70a6115f3204a1b1) (.leaf
  0x16662c189d64a1b1)) (.branch 1 (.leaf 0x2e4f683e18b7a19b1) (.leaf 0x316699e7b9a0c51b1)))
  (.branch 2 (.branch 1 (.leaf 0x337531828c12e9b1) (.leaf 0x475a0cc52372e9b1)) (.branch 1
  (.leaf 0x16d6290c73a6c59b1) (.leaf 0x311899e7b660851b1)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x31c531827016e9b1) (.leaf 0x56210cc5df76e9b1)) (.branch 1 (.leaf
  0x17a7e90c7c66859b1) (.leaf 0x16429bea6d81e19b1))) (.branch 2 (.branch 1 (.leaf
  0x243b322a4c100a9b1) (.leaf 0x3c8b1fe36e60a9b1)) (.branch 1 (.leaf 0x2fb29b01a787e11b1)
  (.branch 1 (.leaf 0x2395c3843295911b1) (.leaf 0x2dc69a4413047a1b1)))))))))))) (.branch 517
  (.branch 258 (.branch 129 (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch
  2 (.branch 1 (.leaf 0x15ed199069f27a1b1) (.leaf 0xbe0e36ff893919b1)) (.branch 1 (.leaf
  0x50e02b65984f51b1) (.leaf 0x12d4c849c8e51e9b1))) (.branch 2 (.branch 1 (.leaf
  0x30b14b9db2131e9b1) (.leaf 0x859e25d9382f59b1)) (.branch 1 (.leaf 0x4ce02b65644b51b1)
  (.leaf 0x12aa2849c7255e9b1)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x31ca5b9dbdd35e9b1)
  (.leaf 0x8a5e25d9c42b59b1)) (.branch 1 (.leaf 0x1e080bb8da5d19b1) (.leaf
  0x1023f97bac343a9b1))) (.branch 2 (.branch 1 (.leaf 0x1420daafd6c23a9b1) (.leaf
  0xa9a605047a3d11b1)) (.branch 1 (.leaf 0xd7e1a298ff0741b1) (.leaf 0x2c440d61e919f9b1)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x5df330264679f9b1) (.leaf
  0x128d6ac245f6749b1)) (.branch 1 (.leaf 0x13e148245411109b1) (.leaf 0x273da1e47580fb9b1)))
  (.branch 2 (.branch 1 (.leaf 0x218f2300f76fb9b1) (.leaf 0xed148cf9e17101b1)) (.branch 1
  (.leaf 0x149aa8245bd1509b1) (.leaf 0x279da1e47a40bb9b1)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x3dc23000b6bb9b1) (.leaf 0xdaa68cf91d7501b1)) (.branch 1 (.leaf 0x1091991630c0349b1)
  (.leaf 0x2e693e9a1a1df1b1))) (.branch 2 (.branch 1 (.leaf 0x252e603ddb57df1b1) (.leaf
  0x378179fdfac6341b1)) (.branch 1 (.leaf 0x35d6ee9f69067a1b0) (.leaf
  0x21dd77888d92919b0)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x27769462f8b0919b0) (.leaf 0x1032ce4aacd47a9b0)) (.branch 1 (.leaf 0x30c4cc92b2e71e9b0)
  (.leaf 0x2611f6bae683f59b0))) (.branch 2 (.branch 1 (.leaf 0x266e55093a1f59b0) (.leaf
  0x372c4c4777351e1b0)) (.branch 1 (.leaf 0x31b9ec92bd275e9b0) (.leaf 0x2649f6bae943b59b0))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2aee5509c61b59b0) (.leaf 0x37559c4778f55e1b0))
  (.branch 1 (.leaf 0x34132da0d6363a9b0) (.leaf 0x396f4b732a2d11b0))) (.branch 2 (.branch 1
  (.leaf 0x428475d4780d11b0) (.leaf 0xddbad7513e43a1b0)) (.branch 1 (.leaf 0x5de97c2e467bf9b0)
  (.leaf 0x107f9deab003549b0))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x327a4e00c521549b0) (.leaf 0x28de571721b5bf1b0)) (.branch 1 (.leaf 0x218c6f08f76db9b0)
  (.leaf 0x161ccfe76be2301b0))) (.branch 2 (.branch 1 (.leaf 0xee1cc0d1ec0301b0) (.leaf
  0xad656254aa4db1b0)) (.branch 1 (.leaf 0x3e56f080b69b9b0) (.leaf 0x15621fe76422701b0))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xd96dc0d1100701b0) (.leaf 0xa6e562545649b1b0))
  (.branch 1 (.leaf 0x252dc4fd5b57ff1b0) (.leaf 0xd6c1ed50f33141b0))) (.branch 2 (.branch 1
  (.leaf 0x37705d3f7a11141b0) (.leaf 0x8b7b4289e85ff9b0)) (.branch 1 (.leaf
  0x2d146cad0b978f9b0) (.leaf 0x258846855ff3649b0))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x343f56f2ad1649b0) (.leaf 0x3354cc78ce458f1b0))
  (.branch 1 (.leaf 0x150b1d9f6086eb9b0) (.leaf 0x20aea4888412001b0))) (.branch 2 (.branch 1
  (.leaf 0x26e1f762f130001b0) (.leaf 0x2f7e4d4aa554eb1b0)) (.branch 1 (.leaf
  0x166ced9f6f46ab9b0) (.leaf 0x21a2e4888bd2401b0)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x27f50762fef0401b0) (.leaf 0x2ffc4d4aaa94ab1b0)) (.branch 1 (.leaf 0x30ee4f92b4a7cf1b0)
  (.leaf 0x59695bae0c3241b0))) (.branch 2 (.branch 1 (.leaf 0x2286965095e1241b0) (.leaf
  0x36a14f477175cf9b0)) (.branch 1 (.leaf 0x23bd46cf36064a9b0) (.leaf 0x33bc2fd8d292a11b0)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2fb72c32a7b0a11b0) (.leaf
  0x2bcd961af3d44a1b0)) (.branch 1 (.leaf 0x26a254c2ede72e1b0) (.leaf 0x11639eeab983c51b0)))
  (.branch 2 (.branch 1 (.leaf 0x332e1d00cca1c51b0) (.leaf 0x91e941728352e9b0)) (.branch 1
  (.leaf 0x25b344c2e2276e1b0) (.leaf 0x11159eeab643851b0)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x324fdd00c361851b0) (.leaf 0x91b941727f56e9b0)) (.branch 1 (.leaf
  0x14ea5f089360a1b0) (.leaf 0x36464ce76da2e19b0))) (.branch 2 (.branch 1 (.leaf
  0x2e4adf0d1880e19b0) (.leaf 0xafe95254ce40a9b0)) (.branch 1 (.leaf 0xfed7e5029f20b1be)
  (.leaf 0x2b0cf747cd66e09be)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x29c614adb844e09be) (.leaf 0x36218e85ec200b9be)) (.branch 1 (.leaf
  0xd117c5c0b77ef9be) (.leaf 0x257826745f13049be))) (.branch 2 (.branch 1 (.leaf
  0x33ff59e2a31049be) (.leaf 0x335e1c89cea5ef1be)) (.branch 1 (.leaf 0xd0ffc620b63af9be)
  (.leaf 0x2b7c764a5f07449be)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x933c5a02a25449be)
  (.leaf 0x135f0cb7ceb1af1be)) (.branch 1 (.leaf 0x2e587d5199164b9be) (.leaf
  0x7dcf4467d82a01be))) (.branch 2 (.branch 1 (.leaf 0x13b67ac08a0a01be) (.leaf
  0x34b14d845cc44b1be)) (.branch 1 (.leaf 0x31154c22467ee9be) (.leaf 0x367f9eea7003059be)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xc79bd000521059be) (.leaf
  0x2b85b417e1b5ee1be)) (.branch 1 (.leaf 0x29b145f1b6120a9be) (.leaf 0x33bb1ce65286e11be)))
  (.branch 2 (.branch 1 (.leaf 0x2fb5bf0c27a4e11be) (.leaf 0x716052473c00a1be)) (.branch 1
  (.leaf 0x3bd75cfb6064a9be) (.leaf 0x33bc1cd85292a11be)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2fb71f3227b0a11be) (.leaf 0xbcdf51a73d44a1be)) (.branch 1 (.leaf
  0x86767c39483ae1be) (.leaf 0x12149debc0e7451be))) (.branch 2 (.branch 1 (.leaf
  0x31094e01b5c5451be) (.leaf 0x46557165151ae9be)) (.branch 1 (.leaf 0x32654f93c443de9be)
  (.branch 1 (.leaf 0x82195bb9027359be) (.leaf 0x2b946651e505359be))))))))) (.branch 64
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xc240f460191de1be) (.leaf 0x34131ea056363a9be)) (.branch 1 (.leaf 0x2396c7b7b2a2d11be)
  (.leaf 0x2428745dc780d11be))) (.branch 2 (.branch 1 (.leaf 0xddb9e7593e43a1be) (.leaf
  0x34121e9e56227a9be)) (.branch 1 (.leaf 0x98af789b2b6911be) (.leaf 0xa942463c794911be))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2ddd0e4b93f07a1be) (.leaf 0x16eecc9274a79e1be))
  (.branch 1 (.leaf 0x2d9a6ba20c3751be) (.leaf 0x24c0f55055e1751be))) (.branch 2 (.branch 1
  (.leaf 0x10a24c47b1759e9be) (.leaf 0x77f563e79263b9be)) (.branch 1 (.leaf
  0xec7cf299db2d01be) (.leaf 0x15cc3cc3e890d01be))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x29ed96ebbcf43b1be) (.leaf 0xb6df4325ba3df1be)) (.branch 1 (.leaf
  0xd799e1a0fc7341be) (.leaf 0x3783bdf07ae5341be))) (.branch 2 (.branch 1 (.leaf
  0x22bf84e79e71df9be) (.leaf 0x536040c5bb79f1be)) (.branch 1 (.leaf 0xd7b1e240fd3741be)
  (.leaf 0x37859dce7af1741be)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x8b3b4d99e659f9be)
  (.leaf 0x2ac3553fc9c27b1be)) (.branch 1 (.leaf 0x303f4c282d56909be) (.leaf
  0x344a4fc25874909be))) (.branch 2 (.branch 1 (.leaf 0x21b1c5ea0c107b9be) (.leaf
  0x2c5c7fc383e00f80f)) (.branch 1 (.leaf 0x2048843180e04000f) (.leaf
  0x279307e5fa164000f)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x12ebef2849e60f00f) (.leaf 0x2731f7d9f5154000f)) (.branch 1 (.leaf 0x12a3df1446e50f00f)
  (.leaf 0x31a0fcc03c130f00f))) (.branch 2 (.branch 1 (.leaf 0x29f277323f134080f) (.leaf
  0x2022e43380374000f)) (.branch 1 (.leaf 0x30d8bcfe33c70f00f) (.leaf 0x12dbff2a49310f00f))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2acb04d84a314080f) (.leaf 0x1293ff1646320f00f))
  (.branch 1 (.leaf 0x2a69f4e445324080f) (.leaf 0x9f747303fc44080f))) (.branch 2 (.branch 1
  (.leaf 0xd230ffd8c340f80f) (.leaf 0x10c68cc233044f00f)) (.branch 1 (.leaf
  0x81b740f80f40000f) (.leaf 0xbe6f7dbfa020000f))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x3756ec29f9024f80f) (.leaf 0xbd607e7f5010000f)) (.branch 1 (.leaf
  0x370edc15f6014f80f) (.leaf 0x2d353fc18cf74f80f))) (.branch 2 (.branch 1 (.leaf
  0x23fe470c3f070080f) (.leaf 0x80f740d80230000f)) (.branch 1 (.leaf 0xc4a4fff83234f80f)
  (.leaf 0x176acc2bf9d54f80f)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2432f4e64a250080f)
  (.leaf 0x1722cc17f6d64f80f)) (.branch 1 (.leaf 0x242204da45260080f) (.leaf
  0x403770e3fd00080f))) (.branch 2 (.branch 1 (.leaf 0x11b2ccfc3cd04f00f) (.leaf
  0x12f81cc3ca60cf00f)) (.branch 1 (.leaf 0x278d940e79908000f) (.leaf 0x99d7da03668000f)))))))
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2c081c280066cf80f) (.leaf 0x1b517e60c658000f)) (.branch 1 (.leaf 0x2d6fdc140f65cf80f)
  (.leaf 0x17043fc07593cf80f))) (.branch 2 (.branch 1 (.leaf 0x2a82070dc6638080f) (.leaf
  0x782f40c79478000f)) (.branch 1 (.leaf 0x17751ffe7a47cf80f) (.leaf 0x2c0f9c2a00b1cf80f))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2995e4e7b3418080f) (.leaf 0x2d776c160fb2cf80f))
  (.branch 1 (.leaf 0x29e4d4dbbc428080f) (.leaf 0x2a83670fc6b48080f))) (.branch 2 (.branch 1
  (.leaf 0x32870cfdc5b4cf00f) (.leaf 0x32f90cfdca748f00f)) (.branch 1 (.leaf
  0x2ab9970fc974c080f) (.leaf 0x2999d4dbb382c080f))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2c09ac1600728f80f) (.leaf 0x29e7e4e7bc81c080f)) (.branch 1 (.leaf
  0x2d715c2a0f718f80f) (.leaf 0x17032ffe75878f80f))) (.branch 2 (.branch 1 (.leaf
  0x74e040c7687c000f) (.leaf 0x2abef70dc9a3c080f)) (.branch 1 (.leaf 0x17763fc07a538f80f)
  (.leaf 0x2c0e2c1400a58f80f)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xa217e603a5c000f)
  (.leaf 0x2d75ec280fa68f80f)) (.branch 1 (.leaf 0x1bcd7da0ca6c000f) (.leaf
  0x2747640e7650c000f))) (.branch 2 (.branch 1 (.leaf 0x12862cc3c5a08f00f) (.leaf
  0x294e645d2cf00e801)) (.branch 1 (.leaf 0x167d7faf6ff010001) (.leaf 0xdf7ec7b150610001))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x61484b6e6f60e001) (.leaf
  0xe6ffc471a0510001)) (.branch 1 (.leaf 0x650748ae9f50e001) (.leaf 0x225d775e93030e001)))
  (.branch 2 (.branch 1 (.leaf 0x137f5cacd00310801) (.leaf 0x166a6fad6f2710001)) (.branch 1
  (.leaf 0x22b6a7609cd70e001) (.leaf 0x606a4b4e6210e001)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xf7a9f46a52110801) (.leaf 0x6465488e9220e001)) (.branch 1 (.leaf 0xff2bf7aaa2210801)
  (.leaf 0x33924caed0d410801))) (.branch 2 (.branch 1 (.leaf 0x8f4846323240e801) (.leaf
  0x36c68fc2f3041e001)) (.branch 1 (.leaf 0x281b170f00f400001) (.leaf 0x2be694db7a0200001)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1156ef2939021e801) (.leaf
  0x2bd664e7750100001)) (.branch 1 (.leaf 0x110edf1536011e801) (.leaf 0x13354cc14cf71e801)))
  (.branch 2 (.branch 1 (.leaf 0x3fe740cbf0700801) (.leaf 0x280f170d002300001)) (.branch 1
  (.leaf 0x3249bcff43231e801) (.leaf 0x316a4f2b39d51e801)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x432c7e6ca2500801) (.leaf 0x31224f1736d61e801)) (.branch 1 (.leaf
  0x42237dac52600801) (.leaf 0x2403440ebfd000801))) (.branch 2 (.branch 1 (.leaf
  0x37b24ffcfcd01e001) (.leaf 0x36dd7c0d73f03e001)) (.branch 1 (.leaf 0x2016c4c0800020001)
  (.branch 1 (.leaf 0x7a2c714faf620001) (.leaf 0x316d7ce6b9f63e801)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x7423728f5f520001) (.leaf 0x31257cdab6f53e801)) (.branch 1 (.leaf 0x131ebf0ecc033e801)
  (.leaf 0x9fe77c33ff320801))) (.branch 2 (.branch 1 (.leaf 0x42e4c280d720001) (.leaf
  0x125a7f30c3d73e801)) (.branch 1 (.leaf 0x3159dce4b9213e801) (.leaf 0xad6c4294ad120801))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3111ecd8b6223e801) (.leaf 0xa76341545d220801))
  (.branch 1 (.leaf 0x9f347c13f2420801) (.leaf 0x17a18c337c243e001))) (.branch 2 (.branch 1
  (.leaf 0x28ae64ad1cf42e001) (.leaf 0x14fd7f5f5ff430801)) (.branch 1 (.leaf
  0xf77bc8b250230801) (.leaf 0x4d48446d6f22e801))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0xfef9cb72a0130801) (.leaf 0x510747ad9f12e801)) (.branch 1 (.leaf
  0x22fd77aea3072e801) (.leaf 0x14ff6c5ce00730001))) (.branch 2 (.branch 1 (.leaf
  0x14ea5f5d5f2330801) (.leaf 0x2356a790acd32e801)) (.branch 1 (.leaf 0x4c6a444d6252e801)
  (.leaf 0xdfaffb6952530001)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x5065478d9262e801)
  (.leaf 0xe72ef8a9a2630001)) (.branch 1 (.leaf 0x35124c5ee0d030001) (.leaf
  0x854849313202e001))) (.branch 2 (.branch 1 (.leaf 0x2815d0eb804406006) (.leaf
  0x2f9d6b6e269390806)) (.branch 1 (.leaf 0xf8e0b7425f530806) (.leaf 0x99ae3ce33d2a6806))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3f110183c76c0806) (.leaf
  0x2ff718a22a5156806)) (.branch 1 (.leaf 0x2fdc18b82937f6806) (.leaf 0x226e33d8fe060006)))
  (.branch 2 (.branch 1 (.leaf 0x2379103c30c460806) (.leaf 0x2fa4d88626e3f6806)) (.branch 1
  (.leaf 0x2f83889c258556806) (.leaf 0x9313198352c0006)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x3ec23f03c06a6806) (.leaf 0x2e8358759ad130006)) (.branch 1 (.leaf
  0xe68386f99b790006) (.leaf 0x21ad0d58f9006006))) (.branch 2 (.branch 1 (.leaf
  0x2f8fcb77a60396806) (.leaf 0x95fd3cdb02400806)) (.branch 1 (.leaf 0x299613d7b342a0806)
  (.leaf 0x2e056852159536006))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x100198bbaac150806) (.leaf 0x1b0233e0c16c6006)) (.branch 1 (.leaf 0x21a13240f7066006)
  (.leaf 0x2e5f1b9e1957f0006))) (.branch 2 (.branch 1 (.leaf 0xf9a789fa673f0806) (.leaf
  0x38b31a00a466006)) (.branch 1 (.leaf 0xa5e30003c2c6006) (.leaf 0xe0cfbba15e550006))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e75c86c1a4136006) (.leaf 0x1b4e0d60c66a0006))
  (.branch 1 (.leaf 0x220e20cc0f0000006) (.leaf 0xfeb3b49a9d796806))) (.branch 2 (.branch 1
  (.leaf 0xf86ab51a5a676806) (.leaf 0x299a23ebb381e0806)) (.branch 1 (.leaf
  0x296c13f1b0e740806) (.leaf 0x2e1468741630d6006))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xfe0a89da964b0806) (.leaf 0x22223180fb326006))
  (.branch 1 (.leaf 0x21c7e3020cd586006) (.leaf 0xe864bb81af210006))) (.branch 2 (.branch 1
  (.leaf 0x2f8b28b9a5d610806) (.leaf 0x208e233c030186006)) (.branch 1 (.leaf
  0x2cd326006726006) (.leaf 0xe15cb9c1640b0006)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2e6ca84a19e4d6006) (.leaf 0x22610f00fc340006)) (.branch 1 (.leaf 0x1bd20ea0ca5e0006)
  (.leaf 0x2ffa3b6faa7276806))) (.branch 2 (.branch 1 (.leaf 0x298ed3f23311e6806) (.leaf
  0xe09e87795c670006)) (.branch 1 (.leaf 0xe1ed86d96a0d0006) (.leaf 0x2817b0d7808746006)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x220ed3018f2320006) (.leaf
  0x2e578bbb9904b6006)) (.branch 1 (.leaf 0xe78dba19a6216006) (.leaf 0x3f420243cb580806)))
  (.branch 2 (.branch 1 (.leaf 0x9ad325839180006) (.leaf 0x2e087b9f95b616006)) (.branch 1
  (.leaf 0xe237b8596d0b6006) (.leaf 0x36cd000300720806)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x212e0e98f5346006) (.leaf 0xfe38b6c2984d0806)) (.branch 1 (.leaf
  0x1004bb762ae270806) (.leaf 0x23f913cc3cc5e6806))) (.branch 2 (.branch 1 (.leaf
  0xd89d874907007808) (.leaf 0x1552c8876382d0008)) (.branch 1 (.leaf 0x2e623b531974d0008)
  (.leaf 0x1479689f5a7607008)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xe1a7b6f1677d0008) (.leaf 0x340158a3557507008)) (.branch 1 (.leaf
  0x1072bb772f8307008) (.leaf 0x14a9eb84dc71d0808))) (.branch 2 (.branch 1 (.leaf
  0x354ed8856355d0008) (.leaf 0x2f06db49205707008)) (.branch 1 (.leaf 0x147e589d5aa107008)
  (.leaf 0x2fdf186ea953d0808)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x340658a155a207008)
  (.leaf 0xf976852a650d0808)) (.branch 1 (.leaf 0x14adfb86dca6d0808) (.leaf
  0xef5884a9fa407808))) (.branch 2 (.branch 1 (.leaf 0xa49e03ec3d6d7008) (.leaf
  0x4573f280d400008)) (.branch 1 (.leaf 0x7970026fa2200008) (.leaf 0x216370d509d0d7808)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x735f01af52100008) (.leaf
  0x210370e906d3d7808)) (.branch 1 (.leaf 0x7c0533d7c25d7808) (.leaf 0x9f670f13f2700808)))
  (.branch 2 (.branch 1 (.leaf 0x201f13f0800300008) (.leaf 0x2718630373f1d7808)) (.branch 1
  (.leaf 0x14e40d70907d7808) (.leaf 0x2ac8831b4a0500808)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xee40eb0604d7808) (.leaf 0x2a647327450600808)) (.branch 1 (.leaf 0x9fb40f33ff000808)
  (.leaf 0xaf05000cc02d7008))) (.branch 2 (.branch 1 (.leaf 0xa4ca3cd43e1b7008) (.leaf
  0x47700100e360008)) (.branch 1 (.leaf 0x79443d57a1560008) (.branch 1 (.leaf
  0x2166b32689e7b7808) (.leaf 0x730b3e9751660008))))))))) (.branch 65 (.branch 32 (.branch 16
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2106b31a86e4b7808) (.leaf
  0x7bc90cefc12b7808)) (.branch 1 (.leaf 0x9ef7302bf1060808) (.leaf 0x237003003460008)))
  (.branch 2 (.branch 1 (.leaf 0x714a0f0f3c6b7808) (.leaf 0x215183248930b7808)) (.branch 1
  (.leaf 0xacc40e8ca3260808) (.leaf 0x20f183188633b7808)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xa68b0d4c53160808) (.leaf 0x29fa4300bfc760808)) (.branch 1 (.leaf
  0x2af313f34c35b7008) (.leaf 0xf0fe8b8a0b767008))) (.branch 2 (.branch 1 (.leaf
  0x13ccc84b5345b0808) (.leaf 0xfe83b9f29b3b0808)) (.branch 1 (.leaf 0x35ff68536ab167808)
  (.leaf 0x2fa07ba326b0b0808))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x1587586f65b267808) (.leaf 0xeecbbbb1f4467808)) (.branch 1 (.leaf 0x162fdb48ecb6b0008)
  (.leaf 0x33d4e8495392b0808))) (.branch 2 (.branch 1 (.leaf 0x2d8ceb85109067808) (.leaf
  0x35f868516a6667808)) (.branch 1 (.leaf 0xe6518a29994b0008) (.leaf 0x1580686d656567808))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e1d689e9697b0008) (.leaf 0x1627fb4aec61b0008))
  (.branch 1 (.leaf 0x106f8886af6367008) (.leaf 0x23bb63f136007b10a))) (.branch 2 (.branch 1
  (.leaf 0x13cf1b9f53517c90a) (.leaf 0x2f99e87526737c90a)) (.branch 1 (.leaf
  0x2bccd324f3d27b90a) (.leaf 0x20ad018884007190a)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x13a69ad951a17690a) (.leaf 0xf6b493324837690a)) (.branch 1
  (.leaf 0x2a20a15d41d27110a) (.leaf 0x2117c1928766d190a))) (.branch 2 (.branch 1 (.leaf
  0x33c19ac352c7d690a) (.leaf 0x2fbc192927e5d690a)) (.branch 1 (.leaf 0x2a32514742b4d110a)
  (.leaf 0xdb40d48596db90a)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x151198bae0c7dc10a)
  (.leaf 0x2e0c6b5095e5dc10a)) (.branch 1 (.leaf 0xa06e0014044db10a) (.leaf
  0x2110f1b707359790a))) (.branch 2 (.branch 1 (.leaf 0x33bcbae6d2949090a) (.leaf
  0x2fb7b90ca7b69090a)) (.branch 1 (.leaf 0x2a395162c2e79710a) (.leaf 0x20e640f105c59d90a)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x350c989f60949a10a) (.leaf
  0xe07eb7515b69a10a)) (.branch 1 (.leaf 0x2a002024c0179d10a) (.leaf 0x2100b0eb06a33d90a)))
  (.branch 2 (.branch 1 (.leaf 0x155dc88563f23a10a) (.leaf 0x2e22eb6f16d03a10a)) (.branch 1
  (.leaf 0x2a42103ec3713d10a) (.leaf 0x23b3a292b4a33710a)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1517c9c361023010a) (.leaf 0xde2ca2914203010a)) (.branch 1 (.leaf
  0x2bc3424771713790a) (.leaf 0x2db2c9329227e790a))) (.branch 2 (.branch 1 (.leaf
  0x42762634786e090a) (.leaf 0x397518932a4e090a)) (.branch 1 (.leaf 0x143e49e757f5e710a)
  (.branch 1 (.leaf 0x2d93687490d7ed90a) (.leaf 0x273d001af586ea10a)))))))) (.branch 32
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3803f080a4ea10a) (.leaf
  0x13f748a15505ed10a)) (.branch 1 (.leaf 0xdd7986e93b14d90a) (.leaf 0x2755f000f6e04a10a)))
  (.branch 2 (.branch 1 (.leaf 0xa293ea83c24a10a) (.leaf 0x3418b8bb56634d10a)) (.branch 1
  (.leaf 0x2f286a1721b14710a) (.leaf 0x271b4146f4104010a)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x204eb2ac81324010a) (.leaf 0x1568bac2e4634790a)) (.branch 1 (.leaf
  0xddc384b13e20b90a) (.leaf 0x274f702576b30c10a))) (.branch 2 (.branch 1 (.leaf
  0x9da3cf03910c10a) (.leaf 0x3413b89ed6300b10a)) (.branch 1 (.leaf 0xf2cea32a1e20110a) (.leaf
  0x722016374430610a))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x59b28901610610a) (.leaf 0x35639ae764300190a)) (.branch 1 (.leaf 0x2f3b4a28a284a110a)
  (.leaf 0x75cb1797725a610a))) (.branch 2 (.branch 1 (.leaf 0x6bb2930207a610a) (.leaf
  0x15af3afd6756a190a)) (.branch 1 (.leaf 0x2f0a6b6ea074ab10a) (.leaf 0x2420a300c525ac90a))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x36ba0eab007ac90a) (.leaf 0x1586bbbb65a6ab90a))
  (.branch 1 (.leaf 0xf93db6e26347a904) (.leaf 0x9b7531bb6a71d104))) (.branch 2 (.branch 1
  (.leaf 0xaf8e0cfcc511d104) (.leaf 0x16230b85ec327a104)) (.branch 1 (.leaf
  0x20991920ee640104) (.leaf 0x305acad82e8527104)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x33e9790c547327104) (.leaf 0x2a620179c4e040904)) (.branch 1
  (.leaf 0x7441b60254e0104) (.leaf 0xf33dafc223787104))) (.branch 2 (.branch 1 (.leaf
  0x1451592858c187104) (.leaf 0xaa9415dc852e0904)) (.branch 1 (.leaf 0xe79d8759a76da104)
  (.leaf 0x2188b0000ae5bd904)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x6cc23d47013bd904)
  (.leaf 0x1389689e5070da904)) (.branch 1 (.leaf 0xded7afd949316104) (.leaf
  0x9ac51b7b4f071104))) (.branch 2 (.branch 1 (.leaf 0x2b175263ce0671104) (.leaf
  0x34dc0a165e9516904)) (.branch 1 (.leaf 0x21c1533e0cb12c104) (.leaf 0xea1cb4b9c224b904)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x15a2789fe6d44b904) (.leaf
  0xa83f3d5c6b72c904)) (.branch 1 (.leaf 0x200e631a00038c104) (.leaf 0xd8d7b6f9090eb904)))
  (.branch 2 (.branch 1 (.leaf 0x15f8f8bbea66eb904) (.leaf 0x2ac773f1ca058c904)) (.branch 1
  (.leaf 0xfd379e628d1b6904) (.leaf 0x140f2ac08b2d1904)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x6f9d1787244d1904) (.leaf 0x3542690de2d7b6104)) (.branch 1 (.leaf
  0x21f592460e5566104) (.leaf 0x1053590c2e3601104))) (.branch 2 (.branch 1 (.leaf
  0x13f1bad854c001104) (.leaf 0x2a5942adc45366904)) (.branch 1 (.leaf 0x2e19eb8596775c104)
  (.branch 1 (.leaf 0x210843f006e43b904) (.leaf 0x7bb60247c123b904))))))))))) (.branch 258
  (.branch 129 (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x34aa7b6e5c715c904) (.leaf 0x2e815ba19ac5fc104)) (.branch 1 (.leaf
  0x2173b3d40a569b904) (.leaf 0x6d4e00070a09b904))) (.branch 2 (.branch 1 (.leaf
  0x13919b4a50c3fc904) (.leaf 0x2981a15db217c6904)) (.branch 1 (.leaf 0xdba6a179274a1904)
  (.leaf 0x35cab9c3e882a1904)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x276c41b67811c6104)
  (.leaf 0x21ac50ea0c020a104)) (.branch 1 (.leaf 0x2eac589f9c916d904) (.leaf
  0x3598bb4be6676d904))) (.branch 2 (.branch 1 (.leaf 0x2a78f001c6040a904) (.leaf
  0xf72ea1624d030904)) (.branch 1 (.leaf 0x20c0f15c04b357904) (.leaf 0x27ed52887e4557904)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3662dafdeed630104) (.leaf
  0x2fc8fa32286290904)) (.branch 1 (.leaf 0x212cf1780801f7904) (.leaf 0x270552ac72f7f7904)))
  (.branch 2 (.branch 1 (.leaf 0x35389ad9e26490104) (.leaf 0x96563f1b040aa904)) (.branch 1
  (.leaf 0x2f136b8420d3cd104) (.leaf 0x1471b8505a25cd104)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x79af31a7a46aa104) (.leaf 0x23d9612638d0d7106)) (.branch 1 (.leaf
  0x34c82abbddb6b0906) (.leaf 0x2fcd2951a894b0906))) (.branch 2 (.branch 1 (.leaf
  0x2bf5d1f3fd02d7906) (.leaf 0x218a40ac0ae7bd906)) (.branch 1 (.leaf 0x14f1980e5f71da906)
  (.leaf 0xff6dbe42a53da906)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xb2fe079cf35bd106) (.leaf 0x215cb0b609811d906)) (.branch 1 (.leaf
  0x14a0c8145c177a906) (.leaf 0xfdbdbfe29357a906))) (.branch 2 (.branch 1 (.leaf
  0xaf81063cc531d106) (.leaf 0x2193c2038b4677906)) (.branch 1 (.leaf 0x3652099e6e2010106)
  (.leaf 0x2e870a741b0210106)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2b1ee2d64e9477106)
  (.leaf 0x176b0b58a77bb906)) (.branch 1 (.leaf 0x14fcf817dfe1dc906) (.leaf
  0x30015bfdaac3dc906))) (.branch 2 (.branch 1 (.leaf 0xb3710604fa5bb106) (.leaf
  0x13ef20008b0d1906)) (.branch 1 (.leaf 0x364b799dedd6b6106) (.leaf 0xe55ca7798f4b6106)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2b0c52d5cd62d1106) (.leaf
  0x1a5321a0bd671906)) (.branch 1 (.leaf 0x36607987eeb016106) (.leaf 0xe949a6d9b9216106)))
  (.branch 2 (.branch 1 (.leaf 0x2b1852cfce0471106) (.leaf 0x23e7539039e11b106)) (.branch 1
  (.leaf 0x362a7b326c777c106) (.leaf 0xe5ed8d819557c106)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2bf0b345fc331b906) (.leaf 0x2d90380e10b1cb906)) (.branch 1 (.leaf
  0x42060ac4527ac906) (.leaf 0x236d93463005ac906))) (.branch 2 (.branch 1 (.leaf
  0x3400e8dbd563cb106) (.leaf 0xdba3abb9276a1906)) (.branch 1 (.leaf 0x759c1267710c6106)
  (.leaf 0x2071b2cc0232c6106))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x34361a6e57a4a1106) (.leaf 0x2d98caa1911001906)) (.branch 1 (.leaf
  0x2724b13c747666106) (.leaf 0x54b2d6015466106))) (.branch 2 (.branch 1 (.leaf
  0x13f1ea7454c201106) (.leaf 0x2f4a0b2ba3276b106)) (.branch 1 (.leaf 0x750c389f6b10c106)
  (.leaf 0x209b906383930c106)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x35a58bfe66f56b906)
  (.leaf 0x2dc4baa212e6a7906)) (.branch 1 (.leaf 0x762b13ff780c0106) (.leaf
  0x7f42d582a2c0106))) (.branch 2 (.branch 1 (.leaf 0x342c6a77d734a7106) (.leaf
  0x2f133b2820d1cd106)) (.branch 1 (.leaf 0x2738f38a7547aa106) (.leaf 0x202af0600065aa106)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x15774bfde503cd906) (.leaf
  0xf579b3223b76d106)) (.branch 1 (.leaf 0x743f39076210a106) (.leaf 0x8d607a03030a106)))
  (.branch 2 (.branch 1 (.leaf 0x3598ebe7e6656d906) (.leaf 0xf222987a17007106)) (.branch 1
  (.leaf 0x241b521a441660906) (.leaf 0x237f61f0313460906)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x156ea95264a207906) (.leaf 0xfd499b928e4d6908)) (.branch 1 (.leaf
  0x9c4a23f3840d1108) (.leaf 0x2a2ea1eb42b6d1108))) (.branch 2 (.branch 1 (.leaf
  0x35438952e2e2d6108) (.leaf 0x1fd0b680018c108)) (.branch 1 (.leaf 0xf07180f20558b108) (.leaf
  0x347e9bdb5aa38b108)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xac9005d4a078c908) (.leaf 0x1c260928cb32c108)) (.branch 1 (.leaf 0x3033f82b2ce72b108)
  (.leaf 0x14104bff56112b108))) (.branch 2 (.branch 1 (.leaf 0x2a84a07946b52c908) (.leaf
  0xdee9aa294a676108)) (.branch 1 (.leaf 0x20adf124840271908) (.leaf 0x27f2e2f0fef471908))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x34ddea495ea076908) (.leaf 0x2e6aebff19d13a108))
  (.branch 1 (.leaf 0x9d75346b9853d108) (.leaf 0x2a3fe092c3733d108))) (.branch 2 (.branch 1
  (.leaf 0x13da0b14d3d73a908) (.leaf 0x206541cf01c460108)) (.branch 1 (.leaf
  0xda06a49116067908) (.leaf 0x1614e99d6b9667908))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0xaec4124cbc260908) (.leaf 0x1d9a1eb0d76c0108)) (.branch 1 (.leaf
  0x2eca7a6d1dd2c7908) (.leaf 0x35a9c9b96724c7908))) (.branch 2 (.branch 1 (.leaf
  0xa91a100c770c0908) (.leaf 0xf84e8e4a5939a908)) (.branch 1 (.leaf 0x20e4b05d05c79d908)
  (.leaf 0x27f7e3897f319d908)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3674680f6f959a108)
  (.leaf 0x21c2a37a8cc34a108)) (.branch 1 (.leaf 0x302c5bc32c974d108) (.leaf
  0x3418e81756614d108))) (.branch 2 (.branch 1 (.leaf 0xa89039146c54a908) (.leaf
  0x2df3194a94d610108)) (.branch 1 (.leaf 0xb702cc847217908) (.branch 1 (.leaf
  0x27f0a118fe8417908) (.leaf 0x14e379a15ed010908))))))))) (.branch 64 (.branch 32 (.branch 16
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xe48596e9864b0108) (.leaf
  0x214302e888c0b7908)) (.branch 1 (.leaf 0x6f4a13cf236b7908) (.leaf 0x13b869855262b0908)))
  (.branch 2 (.branch 1 (.leaf 0x296690613081ea908) (.leaf 0x2d9338d890d5ed908)) (.branch 1
  (.leaf 0x15f1bb0cea23ed908) (.leaf 0x7a1008afa87ea108)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1cb62030d06a6108) (.leaf 0x2ec5d9851da2a1908)) (.branch 1 (.leaf
  0x15af6a516754a1908) (.leaf 0xa8e42e8c700a6908))) (.branch 2 (.branch 1 (.leaf
  0x2f8c6b0ca5e3fc908) (.leaf 0x20e043b505b7fb908)) (.branch 1 (.leaf 0x7fde0617f41fb908)
  (.leaf 0x167cfbe76fe5fc108))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xfdedb28a9515c908) (.leaf 0x214d439109055b908)) (.branch 1 (.leaf 0x717e04573f35b908)
  (.leaf 0x154f1bc363575c108))) (.branch 2 (.branch 1 (.leaf 0x9775118b14406908) (.leaf
  0xf2cba9ea1e001108)) (.branch 1 (.leaf 0x1488394adb1601108) (.leaf 0x7b241f37b4206108))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2f046b852030ad10c) (.leaf 0x2a6b03eb4561aa90c))
  (.branch 1 (.leaf 0x964a0013043aa90c) (.leaf 0x358b8b50e5e2ad90c))) (.branch 2 (.branch 1
  (.leaf 0x148c28a88d5f790c) (.leaf 0x34c219db5d74f090c)) (.branch 1 (.leaf
  0xfc77a312856f090c) (.leaf 0xb04a25f4d07f710c)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x20b4c2ae84675790c) (.leaf 0x13a969ff51c65090c)) (.branch 1
  (.leaf 0x2f745a1524e45090c) (.leaf 0xa1ca27b41b55710c))) (.branch 2 (.branch 1 (.leaf
  0x2ea9689e9c720d90c) (.leaf 0x78100f0f9230a10c)) (.branch 1 (.leaf 0x21ab931a8c010a10c)
  (.leaf 0x1466b84b59a00d10c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2dbee9e512a0a190c)
  (.leaf 0x2a8bb2b4c701a690c)) (.branch 1 (.leaf 0x983615eb223a690c) (.leaf
  0x14310930d772a110c))) (.branch 2 (.branch 1 (.leaf 0x218043d50ab5fb90c) (.leaf
  0x367c9bbb6fe4fc10c)) (.branch 1 (.leaf 0xe8168511ac6fc10c) (.leaf 0xb351300cf67fb10c)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xebb3f106075b90c) (.leaf
  0x354f7b9f63565c10c)) (.branch 1 (.leaf 0xe19d87516745c10c) (.leaf 0xa481324c3d55b10c)))
  (.branch 2 (.branch 1 (.leaf 0x3063eafeaee20110c) (.leaf 0x27b0b1af7b430610c)) (.branch 1
  (.leaf 0x1f752450e610610c) (.leaf 0x360c3a2b6b300190c)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x134c15e8866d190c) (.leaf 0x14c8da0f5dc7d690c)) (.branch 1 (.leaf
  0x2fd4f9e528e5d690c) (.leaf 0x2b0f218b4db4d110c))) (.branch 2 (.branch 1 (.leaf
  0xd8a7b6e90738b90c) (.leaf 0x7340300f5228c10c)) (.branch 1 (.leaf 0x202030ea80008c10c)
  (.leaf 0x3406fbbb55a18b10c))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2eb0fb4a9cc12b90c) (.leaf 0x78ca324f9902c10c)) (.branch 1 (.leaf
  0x21c090ce8cb22c10c) (.leaf 0x34584b9f59132b10c))) (.branch 2 (.branch 1 (.leaf
  0x99f924534247110c) (.leaf 0x1522b914e1857610c)) (.branch 1 (.leaf 0x2deefafe94a77610c)
  (.leaf 0x6eea290f1f67190c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x16d40010a06dd90c)
  (.leaf 0x166e586f6f57da10c)) (.branch 1 (.leaf 0x2e79eb851a75da10c) (.leaf
  0xb3cd0d4cfd4dd10c))) (.branch 2 (.branch 1 (.leaf 0x2f44690ea2e38710c) (.leaf
  0x760b25f77428010c)) (.branch 1 (.leaf 0x2077b1b502608010c) (.leaf 0x35abe9db67318790c)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3056792aae512710c) (.leaf
  0x7b7527b7bf02010c)) (.branch 1 (.leaf 0x220351910ed22010c) (.leaf 0x1612c9ff6b832790c)))
  (.branch 2 (.branch 1 (.leaf 0x29b5931ab6447d10c) (.leaf 0x13c83b74d3157a90c)) (.branch 1
  (.leaf 0x2f93e89ea6377a90c) (.leaf 0x71113cf73967d90c)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x36c631a3004ac902) (.leaf 0x2f0d6b6fa097cb102)) (.branch 1 (.leaf
  0x3478b8bbda61cb102) (.leaf 0xbe853f1fa02ac102))) (.branch 2 (.branch 1 (.leaf
  0x7042900233c6102) (.leaf 0x2f36f9da2250a1102)) (.branch 1 (.leaf 0x144eba0e58a6a1102)
  (.leaf 0x2aa5c27bc835c6902)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2056428a015566102) (.leaf 0x2f1c69c0213601102)) (.branch 1 (.leaf
  0x14992a145bc001102) (.leaf 0xadfb261cb5366902))) (.branch 2 (.branch 1 (.leaf
  0x9e603f83920c102) (.leaf 0x2dc7084a13016b902)) (.branch 1 (.leaf 0x15ed8b9e69f76b902)
  (.leaf 0x2abcc0d449940c902)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x204b42af810620102)
  (.leaf 0xf20e9e5a16547102)) (.branch 1 (.leaf 0x14953a31db9347102) (.leaf
  0x2adab2444b0020902))) (.branch 2 (.branch 1 (.leaf 0xa3501a03c14a102) (.leaf
  0xdcea86f93522d902)) (.branch 1 (.leaf 0x15e6bbbbe9a42d902) (.leaf 0xac600f1c9c74a902)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x38600000a7ea102) (.leaf
  0x2d84687590348d902)) (.branch 1 (.leaf 0x36017ba1eac28d902) (.leaf 0xad4f0ebcaa1ea902)))
  (.branch 2 (.branch 1 (.leaf 0x2395918a329080902) (.leaf 0xdc64ac012f3e7902)) (.branch 1
  (.leaf 0x35bfc9146805e7902) (.leaf 0xbe1c161f89680102)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2de14a2a141450102) (.leaf 0x23b06160347737102)) (.branch 1 (.leaf
  0x445e2b44e8137102) (.leaf 0x34d14ac1de1250902))) (.branch 2 (.branch 1 (.leaf
  0xe22d89f96d33a102) (.leaf 0xf540ea06405d902)) (.branch 1 (.leaf 0x27c9e33e7cb65d902)
  (.branch 1 (.leaf 0x14b2f8745cd53a902) (.leaf 0x2e07d88595b59a102)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xd1b0f00526fd902) (.leaf 0x280593247fd0fd902)) (.branch 1 (.leaf 0x34f7a86e5fb39a902)
  (.leaf 0x2fb3090fa782f0902))) (.branch 2 (.branch 1 (.leaf 0x2128c24587e197902) (.leaf
  0x27cee191fd1797902)) (.branch 1 (.leaf 0x164309e46d84f0102) (.leaf 0xe0c58a015e6dc102))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xd6b0d58575bb902) (.leaf 0x7ff1301ff83bb902))
  (.branch 1 (.leaf 0x34fc984bdfe0dc902) (.leaf 0xfbaa92a27d1b6902))) (.branch 2 (.branch 1
  (.leaf 0x211ff26007b2d1902) (.leaf 0x7d9a1b47d44d1902)) (.branch 1 (.leaf
  0x164b19c1edd7b6102) (.leaf 0xf6ff93024b716902))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0xc9327a04d471902) (.leaf 0x27e9d1ae7e2271902)) (.branch 1 (.leaf
  0x166019dbeeb116102) (.leaf 0xf99db85a6707c902))) (.branch 2 (.branch 1 (.leaf
  0x3c9a3f036e31b102) (.leaf 0x243c20244c151b102)) (.branch 1 (.leaf 0x162a1b6e6c767c102)
  (.leaf 0x2f1c396c213401100)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xa59b2f1c45266900)
  (.leaf 0x97d911bb17066900)) (.branch 1 (.leaf 0x157389b9e4e601900) (.leaf
  0x168b39009e63b900))) (.branch 2 (.branch 1 (.leaf 0x14aa1b325c705c900) (.leaf
  0x2fdee8d829525c900)) (.branch 1 (.leaf 0xaf51345cc343b100) (.leaf 0x20d3b3b405549b900))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x3391fb1650c2fc900) (.leaf
  0xf8c58fc25e0fc900)) (.branch 1 (.leaf 0xa0e1361c0869b100) (.leaf 0xec16a779d76a1900)))
  (.branch 2 (.branch 1 (.leaf 0x76db1ea7810c6100) (.leaf 0x1d1a2000d32c6100)) (.branch 1
  (.leaf 0x144eeaa258a4a1100) (.leaf 0x2d8438d990368d900)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2a70f07bc5a0ea900) (.leaf 0x29675391b082ea900)) (.branch 1 (.leaf
  0x340b880c55e48d100) (.leaf 0x12f311a0814b7900))) (.branch 2 (.branch 1 (.leaf
  0x1641da87ed72d0100) (.leaf 0x2e46e96d9850d0100)) (.branch 1 (.leaf 0x2b1551cfcdc6b7100)
  (.leaf 0xbb313e04a617900))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x3529faa3e1c070100) (.leaf 0xdf4994994e270100)) (.branch 1 (.leaf 0xa1951ebc17417100)
  (.leaf 0x30296bc22c742d100))) (.branch 2 (.branch 1 (.leaf 0x2790f36079e24a100) (.leaf
  0x21c3608a0cc04a100)) (.branch 1 (.leaf 0x15e6eb17e9a62d900) (.leaf 0xd1405c0524fd900))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x338f58fe50b29a900) (.leaf 0x2f84db1425909a900))
  (.branch 1 (.leaf 0x2a10b089c0f6fd100) (.leaf 0x2eb6c99f9d06c7900))) (.branch 2 (.branch 1
  (.leaf 0x276ef2027860a0100) (.leaf 0x1d361e80d42a0100)) (.branch 1 (.leaf
  0x3452794a58d4c7100) (.leaf 0x2da7d9bb91b467900))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x72bb22674d200100) (.leaf 0x2068b1cc01f000100))
  (.branch 1 (.leaf 0x13e8596e546667100) (.leaf 0x29d59347b9665d100))) (.branch 2 (.branch 1
  (.leaf 0x16353be5ecf03a100) (.leaf 0xe6ad80f99d23a100)) (.branch 1 (.leaf
  0x27c813927cb45d900) (.leaf 0xc9c2d604d671900)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x3527594be1b016100) (.leaf 0x2ded1aa1949216100)) (.branch 1 (.leaf 0xa15b203c10471100)
  (.leaf 0x101ec82a2c044b100))) (.branch 2 (.branch 1 (.leaf 0x278bf08879922c100) (.leaf
  0x1c1a3620cb02c100)) (.branch 1 (.leaf 0x35ea78ffe9d64b900) (.leaf 0xf10180e20b6eb100)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2733f0ac75208c100) (.leaf
  0xe034600028c100)) (.branch 1 (.leaf 0x158098dbe564eb900) (.leaf 0x29c961cdb894d1100)))
  (.branch 2 (.branch 1 (.leaf 0x34cd3a505df2b6900) (.leaf 0x2fd319ba28d0b6900)) (.branch 1
  (.leaf 0x7d751187d46d1900) (.leaf 0x237da1f331000090e)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2f26aa7521a40710e) (.leaf 0x148f29a15b520710e)) (.branch 1 (.leaf
  0x2beda118fb060010e) (.leaf 0x8ca38a83000a10e))) (.branch 2 (.branch 1 (.leaf
  0xf4eab3323540d10e) (.leaf 0x1466e8e759a20d10e)) (.branch 1 (.leaf 0x2ab4036149060a90e)
  (.leaf 0x202a93908066aa10e)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2f043b292032ad10e) (.leaf 0x348178fd5ac4ad10e)) (.branch 1 (.leaf
  0xad1037b4a60aa90e) (.leaf 0x207ab2d68296a010e))) (.branch 2 (.branch 1 (.leaf
  0xdb439509232a790e) (.leaf 0x15d1ea84e8c4a790e)) (.branch 1 (.leaf 0xaab423d4890a090e)
  (.leaf 0x209c539303900c10e)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xf593b2aa3c40b10e)
  (.leaf 0x145bb8fed9320b10e)) (.branch 1 (.leaf 0xabb7378c9960c90e) (.leaf
  0x205942d501600610e))) (.branch 2 (.branch 1 (.leaf 0x2da9795311c40190e) (.leaf
  0x360c6a876b320190e)) (.branch 1 (.leaf 0xae5c23ecb660690e) (.leaf 0x206e42cf0206a610e)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2dbeb94912a2a190e) (.leaf
  0x35c6aa9d6854a190e)) (.branch 1 (.leaf 0xa9f3224c800a690e) (.leaf 0x236e50b6b006ac90e)))
  (.branch 2 (.branch 1 (.leaf 0x2d87380f1052ab90e) (.leaf 0x15feebdb6aa4ab90e)) (.branch 1
  (.leaf 0x2be8c05d7a00ac10e) (.leaf 0x2e5eeb2899567c10e)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x3dd939139027b10e) (.leaf 0x2418104543f47b10e)) (.branch 1 (.leaf
  0x33cf7bc353507c90e) (.leaf 0x2e962a6e9ba67610e))) (.branch 2 (.branch 1 (.leaf
  0x218d01e88b027190e) (.leaf 0x6efa23cf1f47190e)) (.branch 1 (.leaf 0x33a6fa8551a07690e)
  (.branch 1 (.leaf 0xe517a7498c0d610e) (.leaf 0x132c1f28864d190e))))))))) (.branch 65
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x26fb2226f292d190e) (.leaf 0x13c1fa9f52c6d690e)) (.branch 1 (.leaf 0x1001680d2ac0dc90e)
  (.leaf 0x17b40b48a94db90e))) (.branch 2 (.branch 1 (.leaf 0x6cee360f062db90e) (.leaf
  0x3511f8e6e0c6dc10e)) (.branch 1 (.leaf 0x2e8bba771b367010e) (.leaf 0x19bf1f10b927790e))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x26e9522571647790e) (.leaf 0x339bba9cd1307090e))
  (.branch 1 (.leaf 0x2fdbe80ea9367a90e) (.leaf 0x15940b709627d90e))) (.branch 2 (.branch 1
  (.leaf 0x70fe36373947d90e) (.leaf 0x154bf8e563307a10e)) (.branch 1 (.leaf
  0x2ff6e814aa50da90e) (.leaf 0x16db0ad0a04dd90e))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x6dd137970f2dd90e) (.leaf 0x1506a8ff6056da10e)) (.branch 1 (.leaf
  0xfcea952a8a0d090e) (.leaf 0x3cca2d4b804d710e))) (.branch 2 (.branch 1 (.leaf
  0x4132100c2f2d710e) (.leaf 0x353ea9b962a6d010e)) (.branch 1 (.leaf 0x2bdfa12778940c00c)
  (.leaf 0x2fdf7832a952d080c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x10064814aaf73080c)
  (.leaf 0x2aed323ecbc1ec80c)) (.branch 1 (.leaf 0x2408e0913fe54080c) (.leaf
  0x34e2dabb5ed39c80c))) (.branch 2 (.branch 1 (.leaf 0x34c1da9d5d767c80c) (.leaf
  0x21bed3888cb0a000c)) (.branch 1 (.leaf 0x23a420893394a080c) (.leaf
  0x13beaaa352a27c80c)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x1397ca8551079c80c) (.leaf 0x3fc39080c14000c)) (.branch 1 (.leaf 0x241b9200c415ec80c)
  (.leaf 0x2e0b2b1515d33000c))) (.branch 2 (.branch 1 (.leaf 0xe1a1b331676d000c) (.leaf
  0x75f311977400c00c)) (.branch 1 (.leaf 0x100bb96d2b32dc80c) (.leaf 0x2ac873474a040080c))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xabf036149a1e080c) (.leaf 0x2e48fa7498673c00c))
  (.branch 1 (.leaf 0x14afdbe4dcb39080c) (.leaf 0x21d852f10d754c00c))) (.branch 2 (.branch 1
  (.leaf 0x220552d70ed0ac00c) (.leaf 0x367c58fd6fe67000c)) (.branch 1 (.leaf
  0x33916bfcd0c27080c) (.leaf 0x4bf2e90104ac00c))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x7f32cf02a14c00c) (.leaf 0x3554e8e563979000c)) (.branch 1 (.leaf
  0x2e37ba4a97b33c00c) (.leaf 0x274c7060f685e000c))) (.branch 2 (.branch 1 (.leaf
  0x7330046f5200000c) (.leaf 0x2f74995324e6dc80c)) (.branch 1 (.leaf 0x30070a9eab05bc80c)
  (.leaf 0xaccb0b4ca336080c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xabc4092c9968080c)
  (.leaf 0x2e47798718505c00c)) (.branch 1 (.leaf 0x14ab08175c84f080c) (.leaf
  0x21d391028d422c00c))) (.branch 2 (.branch 1 (.leaf 0x20891248ee7cc00c) (.leaf
  0x167abb0eefd11000c)) (.branch 1 (.leaf 0x3395880f50f51080c) (.branch 1 (.leaf
  0x4fc11a8133cc00c) (.leaf 0x207b013c82962c00c)))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x15563b16e3a0f000c) (.leaf 0xe3309b917845c00c))
  (.branch 1 (.leaf 0x750b39376b28000c) (.leaf 0x73043b575176000c))) (.branch 2 (.branch 1
  (.leaf 0x2f731aa0a4d1bc80c) (.leaf 0xaa6c1eb48536c80c)) (.branch 1 (.leaf
  0xe6578fe9995b000c) (.leaf 0xe7428d89a305000c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2bed32f2fb068c00c) (.leaf 0x210e05d0f222000c)) (.branch 1 (.leaf 0x16514a776e14fc00c)
  (.leaf 0x36482a516db11c00c))) (.branch 2 (.branch 1 (.leaf 0x23eed344bc77c080c) (.leaf
  0x209420450353c000c)) (.branch 1 (.leaf 0x15386a6f62651c00c) (.leaf 0x35296a4961c0fc00c)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x236b135cb0062080c) (.leaf
  0x272cc2ccf4d28c00c)) (.branch 1 (.leaf 0x2f794bd925145080c) (.leaf 0x2fa01bff26b1b080c)))
  (.branch 2 (.branch 1 (.leaf 0x242951d547876c80c) (.leaf 0x35ceb9b868a00d802)) (.branch 1
  (.leaf 0x1500480e601150002) (.leaf 0xe84bbda1ae750002)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xf3eb953a2a60d002) (.leaf 0xe0c9be615e450002)) (.branch 1 (.leaf
  0x3045d96fada50d002) (.leaf 0x142f3abbd7530d002))) (.branch 2 (.branch 1 (.leaf
  0x34fc5b0ddfe250802) (.leaf 0x3511680c60c650002)) (.branch 1 (.leaf 0x344aba85d8870d002)
  (.leaf 0xf3a3951a2710d002)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1001f8e7aac050802) (.leaf 0x3041696dad720d002)) (.branch 1 (.leaf
  0xf89e8dba5c350802) (.leaf 0x34eb7b0fdf3550802))) (.branch 2 (.branch 1 (.leaf
  0x35b1098667740d802) (.leaf 0x2a2fd1f1c2b55d002)) (.branch 1 (.leaf 0x27a593787af400002)
  (.leaf 0x10c0ac000200002)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2142411a08b35d802)
  (.leaf 0x220bd0900f0100002)) (.branch 1 (.leaf 0x2122012607b05d802) (.leaf
  0x7d822f27d465d802))) (.branch 2 (.branch 1 (.leaf 0xa66007bc50700802) (.leaf
  0x2796f37a7a2300002)) (.branch 1 (.leaf 0x6fcd2cc72925d802) (.leaf 0x2135b11808645d802)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x9622391b02500802) (.leaf
  0x2117312407675d802)) (.branch 1 (.leaf 0x29f3d3adbf2600802) (.leaf 0x2a736079c5d000802)))
  (.branch 2 (.branch 1 (.leaf 0xb0da1cfcd615d002) (.leaf 0x2a21a1ebc1d3fd002)) (.branch 1
  (.leaf 0x278b63627992a0002) (.leaf 0x98d0b60364a0002)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x21a5c1000bd5fd802) (.leaf 0x1b6108a0c67a0002)) (.branch 1 (.leaf 0xc9b13c04d6fd802)
  (.leaf 0x27e8d2e87e20fd802))) (.branch 2 (.branch 1 (.leaf 0x2a7ef061c661a0802) (.leaf
  0x78603607945a0002)) (.branch 1 (.leaf 0x26f0d2d671f4fd802) (.branch 1 (.leaf
  0x18af1020b02fd802) (.leaf 0x2994e38bb343a0802))))))))))))) (.branch 1034 (.branch 517
  (.branch 258 (.branch 129 (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch
  2 (.branch 1 (.leaf 0x20ae413e0401fd802) (.leaf 0x29e5d3b7bc40a0802)) (.branch 1 (.leaf
  0x2a859063c6b6a0802) (.leaf 0xb1921d5ce07fd002))) (.branch 2 (.branch 1 (.leaf
  0x148c6a9ddb36ad002) (.leaf 0x13d2cb2bd387f0802)) (.branch 1 (.leaf 0x2fe268ffa971f0802)
  (.leaf 0xd9c6a761130ad802)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xf9a18c3a672f0802)
  (.leaf 0xed35a4a1e33ad802)) (.branch 1 (.leaf 0x1571e99e64c5ad802) (.leaf
  0x1629d8286c74f0002))) (.branch 2 (.branch 1 (.leaf 0x33ceeb29d350f0802) (.leaf
  0x160839a06b11ad802)) (.branch 1 (.leaf 0xdacea7411e7ad802) (.leaf 0x2e5f7bc21956f0002)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xee3ea481ee4ad802) (.leaf
  0xe173bfe1655f0002)) (.branch 1 (.leaf 0x162df82a6ca3f0002) (.leaf 0x33f38aa3d4e2ad002)))
  (.branch 2 (.branch 1 (.leaf 0x243b9200cc10c0b3d) (.leaf 0x34af7986dcb4c733d)) (.branch 1
  (.leaf 0x34a86984dc63c733d) (.leaf 0xbefa13d7c37c033d)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x120599eb4040c933d) (.leaf 0x258d8152e014ce33d)) (.branch 1 (.leaf
  0x596e150e0c3ce33d) (.leaf 0x3688fad6f067c9b3d))) (.branch 2 (.branch 1 (.leaf
  0x22ced2baa064f933d) (.leaf 0x2c031a030030fe33d)) (.branch 1 (.leaf 0x2c139a0100e7fe33d)
  (.leaf 0x282321871043f9b3d)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xeb19a6e9cc4f033d) (.leaf 0x1b341e88c60f7b3d)) (.branch 1 (.leaf 0x1beb1ea8cb7f7b3d)
  (.leaf 0x3034f9532ce3f0b3d))) (.branch 2 (.branch 1 (.leaf 0x27f07060fe80cc33d) (.leaf
  0x14e278d95ed4cb33d)) (.branch 1 (.leaf 0x34cf48db5e03cb33d) (.leaf 0x2b24735d4ea7ccb3d))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x323298b4c220c533d) (.leaf 0x24807332d284c2b3d))
  (.branch 1 (.leaf 0x47a5330d253c2b3d) (.leaf 0x16af4b897207c5b3d))) (.branch 2 (.branch 1
  (.leaf 0x22eda3e52204f533d) (.leaf 0x10be786332a0f2b3d)) (.branch 1 (.leaf
  0x10b9e8613277f2b3d) (.leaf 0x284560d89223f5b3d))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x1057180eae54fcb3d) (.leaf 0x21ee40b70e00fbb3d)) (.branch 1 (.leaf
  0x20370b50ed7fbb3d) (.leaf 0xed9fb331e73fc33d))) (.branch 2 (.branch 1 (.leaf
  0x7d30046fd252c33d) (.leaf 0x14c178ff5d712b33d)) (.branch 1 (.leaf 0x14c678fd5da62b33d)
  (.leaf 0x2b05837b4d022cb3d)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x32237892c1852533d)
  (.leaf 0x4608314d12122b3d)) (.branch 1 (.leaf 0x46ea316d1f622b3d) (.leaf
  0x36a6fbaf71a225b3d))) (.branch 2 (.branch 1 (.leaf 0x2e853c321a11533d) (.leaf
  0x10974845310512b3d)) (.branch 1 (.leaf 0x30aae84731d212b3d) (.leaf
  0x283860fe918615b3d))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x104dc828adf11cb3d) (.leaf 0x1e240910da51bb3d)) (.branch 1 (.leaf
  0x1d770930d721bb3d) (.leaf 0x2ecb7b151dd61c33d))) (.branch 2 (.branch 1 (.leaf
  0x7fb31197f452033d) (.leaf 0x167bfa9f6fe127b3d)) (.branch 1 (.leaf 0x166bea9d6f3627b3d)
  (.leaf 0x2b333224cf6220b3d)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x16c81af2f31529b3d)
  (.leaf 0x248b724b53412eb3d)) (.branch 1 (.leaf 0x492124953962eb3d) (.leaf
  0x324b19cf43322933d))) (.branch 2 (.branch 1 (.leaf 0x260e1a3133119b3d) (.leaf
  0x10d0391ab3651eb3d)) (.branch 1 (.leaf 0x10d7b918b3b21eb3d) (.leaf 0x8f1229ea3161933d)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1074b9772f9110b3d) (.leaf
  0x40052f13f351733d)) (.branch 1 (.leaf 0x40962f33fe21733d) (.leaf 0x2ef7ba4a9fb61033d)))
  (.branch 2 (.branch 1 (.leaf 0x6763479eb8515b38) (.leaf 0x3789effffb2112338)) (.branch 1
  (.leaf 0x379deffdfbf612338) (.leaf 0xb6bc7445ba215338)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x35aa9c5de7213c338) (.leaf 0x2a9184e447753b338)) (.branch 1 (.leaf
  0x2a96e4e647a23b338) (.leaf 0x14268f6057063cb38))) (.branch 2 (.branch 1 (.leaf
  0x148273208d10c338) (.leaf 0xfcaef8ba8850b338)) (.branch 1 (.leaf 0x2fc64f89a8520b338)
  (.leaf 0x29cce40fb8f60cb38)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x30eb9c29b48525338) (.leaf 0x8ff57afa42122b38)) (.branch 1 (.leaf
  0x90d97ada4f622b38) (.leaf 0xc6d8f1404a225b38))) (.branch 2 (.branch 1 (.leaf
  0x3376eeba4fa289338) (.leaf 0x6c98603eff68e338)) (.branch 1 (.leaf 0x6bae601ef218e338)
  (.leaf 0x17f3bd87ff8589b38)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2717c5a1f3f6a0338)
  (.leaf 0x154e4e27e352a7b38)) (.branch 1 (.leaf 0x35535e25e385a7b38) (.leaf
  0xa48c69c43d1a0b38))) (.branch 2 (.branch 1 (.leaf 0x2e9feece1c0690338) (.leaf
  0x21bc45480ca297b38)) (.branch 1 (.leaf 0x21b7b54a0c7597b38) (.leaf 0x1022bdf3ac2190b38)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x234d6ea10a2b9b38) (.leaf
  0x1095ee53b0f6beb38)) (.branch 1 (.leaf 0x10825e51b021beb38) (.leaf 0x8c825d7a085b9338)))
  (.branch 2 (.branch 1 (.leaf 0x325aeea243d369338) (.leaf 0x5d5861be3876e338)) (.branch 1
  (.leaf 0x25cae619e3506e338) (.leaf 0x16dded9ff3f469b38)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x27fec5b9ff8740338) (.leaf 0x3669fe3fef2347b38)) (.branch 1 (.leaf
  0x367dee3deff447b38) (.leaf 0xb36c6844fa040b38))) (.branch 2 (.branch 1 (.leaf
  0x2d894ed6107770338) (.leaf 0x43655000d377b38)) (.branch 1 (.leaf 0x2005f552000477b38)
  (.branch 1 (.leaf 0xf064deba05070b38) (.leaf 0x22b926f21cd359b38))))))))) (.branch 64
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x31aafe4bbc875eb38) (.leaf 0x11a64e49bc505eb38)) (.branch 1 (.leaf 0x294ce5cfacf459338)
  (.leaf 0x2b5b975e5704f5338))) (.branch 2 (.branch 1 (.leaf 0x12b5dcd847a0f2b38) (.leaf
  0x12b1ecda4777f2b38)) (.branch 1 (.leaf 0x617c463e723f5b38) (.leaf 0x3495bf7a5ba0dcb38))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x7b987c3fbf4dbb38) (.leaf 0x7aae7c1fb23dbb38))
  (.branch 1 (.leaf 0x3613fc47eb87dc338) (.leaf 0x29a3d415b450ecb38))) (.branch 2 (.branch 1
  (.leaf 0xddedcac1404ebb38) (.leaf 0x2df24cae14d3ebb38)) (.branch 1 (.leaf
  0x20b817280477ec338) (.leaf 0xcbebf0e0804c5b38))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2295948818a0c2338) (.leaf 0x228f548a1877c2338)) (.branch 1 (.leaf
  0x1142fc33b823c5338) (.leaf 0xf161ce520f28b287))) (.branch 2 (.branch 1 (.leaf
  0x2ad504b74aa08ca87) (.leaf 0x966a76130818ca87)) (.branch 1 (.leaf 0x35f18c0cea238ba87)
  (.leaf 0x2c581f9083b283a87)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2501d4fd591084a87)
  (.leaf 0x22ff772b233184a87)) (.branch 1 (.leaf 0x32e02f79496383287) (.leaf
  0x2c569fae83a6c3a87))) (.branch 2 (.branch 1 (.leaf 0xb6584c35904c4a87) (.leaf
  0x8f347152325c4a87)) (.branch 1 (.leaf 0x12e10f474977c3287) (.leaf 0x2d811fe49016cba87))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x79b07b6fa44cc287) (.leaf
  0x202b04608065cc287)) (.branch 1 (.leaf 0x34814f0d5ac7cb287) (.leaf 0x2da94ea311c767a87)))
  (.branch 2 (.branch 1 (.leaf 0xae445cecb6560a87) (.leaf 0x29776618b14460a87)) (.branch 1
  (.leaf 0x34880e4adb1667287) (.leaf 0xc39bee902776fa87)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x263196bb682568287) (.leaf 0x224b356d120468287)) (.branch 1 (.leaf
  0x32ce3e00c8a66f287) (.leaf 0x2c382ed702632fa87))) (.branch 2 (.branch 1 (.leaf
  0xba08685683128287) (.leaf 0x83f0553121028287)) (.branch 1 (.leaf 0x32cf0e3ec8b22f287)
  (.leaf 0x2f1aada2a12327287))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x27b446cf7b8120287) (.leaf 0x61451901a020287)) (.branch 1 (.leaf 0x161e2d4b6bf227a87)
  (.leaf 0x13ac63e88a4f7a87))) (.branch 2 (.branch 1 (.leaf 0x13afad535206f0a87) (.leaf
  0xfc2ae852827f0a87)) (.branch 1 (.leaf 0x2a2ca6d74275f7287) (.leaf 0x891b6749b14ffa87))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x169d2e26f146f8287) (.leaf 0x2d106df08b67f8287))
  (.branch 1 (.leaf 0x46bf69d51c5ff287) (.leaf 0x29d864a9b00bfa87))) (.branch 2 (.branch 1
  (.leaf 0x169e3e18f152b8287) (.leaf 0x2d11edce8b73b8287)) (.branch 1 (.leaf
  0x2b4406a351d1bf287) (.leaf 0x29c4953f3840b7287))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1543be52e2e2b0287) (.leaf 0xe514d8498c3b0287))
  (.branch 1 (.leaf 0x26fca5d6f291b7a87) (.leaf 0x158474709611ba87))) (.branch 2 (.branch 1
  (.leaf 0x154bcf1563331c287) (.leaf 0xe58ecc319121c287)) (.branch 1 (.leaf
  0xa45e7aec3b01b287) (.leaf 0x934b432aa2113287)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x368b3f5f708314287) (.leaf 0xcfe3c890aa214287)) (.branch 1 (.leaf 0x259bb4db60f013a87)
  (.leaf 0x340840caa3553287))) (.branch 2 (.branch 1 (.leaf 0x168c3f61709754287) (.leaf
  0x2cffacb70ab654287)) (.branch 1 (.leaf 0xb7f04e560e453a87) (.leaf 0x29d76446b9855b287)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x33da3c14d3d75ca87) (.leaf
  0x2fedefc2a9f65ca87)) (.branch 1 (.leaf 0x70be4af73545ba87) (.leaf 0x47f92d6d2815f28c)))
  (.branch 2 (.branch 1 (.leaf 0x31526a84b8d358a8c) (.leaf 0x1245e952c2f258a8c)) (.branch 1
  (.leaf 0x2882e23f18505fa8c) (.leaf 0x13cc1a288a5d7a8c)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x13afcacf5207d0a8c) (.leaf 0xfc2c9192826d0a8c)) (.branch 1 (.leaf
  0x2a2ba14b4274d728c) (.leaf 0x11801a2876597a8c))) (.branch 2 (.branch 1 (.leaf
  0x14c8eacf5dc790a8c) (.leaf 0xfbc291927e690a8c)) (.branch 1 (.leaf 0x2b0ee14b4db49728c)
  (.leaf 0x269e41e96db11fa8c)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xcbc49bb07e31828c) (.leaf 0x37c96a6d7dc21828c)) (.branch 1 (.leaf
  0x9164100a7601f28c) (.leaf 0x58e60b6e01153a8c))) (.branch 2 (.branch 1 (.leaf
  0x317f6bdb3ab354a8c) (.leaf 0x120cc80d409254a8c)) (.branch 1 (.leaf 0x936e05f2ac05328c)
  (.leaf 0x184b0fd0ac5dba8c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x150ca8af6097dc28c)
  (.leaf 0xe7feb791ab6dc28c)) (.branch 1 (.leaf 0x9ffe014c014db28c) (.leaf
  0xcdb0fd05059ba8c))) (.branch 2 (.branch 1 (.leaf 0x166e68af6f579c28c) (.leaf
  0xe01eb7915769c28c)) (.branch 1 (.leaf 0xb3d1014cfd49b28c) (.leaf 0x57bb3895f211328c)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2c8338e485831428c) (.leaf
  0x17f63b32ffa21428c)) (.branch 1 (.leaf 0x87bb36095f013a8c) (.leaf 0x371dd81576a6c3a8c)))
  (.branch 2 (.branch 1 (.leaf 0x34b9378ac04c4a8c) (.leaf 0x4c6d0aed625c4a8c)) (.branch 1
  (.leaf 0x31aa78fcbc77c328c) (.leaf 0x2ea9585e9c724ba8c)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x744000cf6204c28c) (.leaf 0x21aba3da8c014c28c)) (.branch 1 (.leaf
  0x341ef8b756a34b28c) (.leaf 0x2dd7a85e93b20ba8c))) (.branch 2 (.branch 1 (.leaf
  0x791000cf9e00c28c) (.leaf 0x20a2a3da83c10c28c)) (.branch 1 (.leaf 0x3460f8b759630b28c)
  (.branch 1 (.leaf 0x12e4cb2ac9968328c) (.leaf 0x2262404713348428c)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2640639169158428c) (.leaf 0xc4dfbc3034783a8c)) (.branch 1 (.leaf 0x36f0d94af4c6cfa8c)
  (.leaf 0x22c291189e94c828c))) (.branch 2 (.branch 1 (.leaf 0x25ea62cee4b5c828c) (.leaf
  0x11d0c9a33e17cf28c)) (.branch 1 (.leaf 0x3063da3eaee24728c) (.leaf 0x2721c15374404028c))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1f762850e614028c) (.leaf 0x1563aad7643347a8c))
  (.branch 1 (.leaf 0x2f1aca3ea1220728c) (.leaf 0x27b541537b800028c))) (.branch 2 (.branch 1
  (.leaf 0x62428501a10028c) (.leaf 0x161e4ad76bf307a8c)) (.branch 1 (.leaf
  0x331dba754bf68f28c) (.leaf 0x22ea022721a488a8c))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x253011f15b8588a8c) (.leaf 0xc1a3a9c81278fa8c)) (.branch 1 (.leaf
  0x502d0ced927c4a88) (.leaf 0x12e2eb48c983c3288))) (.branch 2 (.branch 1 (.leaf
  0x31aa18a0bc76c3288) (.leaf 0x28a0a0191c22c4288)) (.branch 1 (.leaf 0x8c93ba83034c288)
  (.leaf 0xf4e9b0323574b288)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x341e98eb56a24b288)
  (.leaf 0x2a79036d46064ca88)) (.branch 1 (.leaf 0x1c293ba8cc30c288) (.leaf
  0x102c6b032c970b288))) (.branch 2 (.branch 1 (.leaf 0x346098eb59620b288) (.leaf
  0x2ac5f36d49c60ca88)) (.branch 1 (.leaf 0x260463f1661784288) (.leaf
  0x171ff87776b383a88)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xc4d9b9f034683a88) (.leaf 0x28f24326a31284a88)) (.branch 1 (.leaf 0x262a9288e81228288)
  (.leaf 0x32c4ea3148462f288))) (.branch 2 (.branch 1 (.leaf 0x31c7f9d93db32f288) (.leaf
  0x294ea25f2d1728a88)) (.branch 1 (.leaf 0x2085b2c302c6a0288) (.leaf 0xdb8a9451262a7a88))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x35b52aad6797a7a88) (.leaf 0xa9e4214c7c3a0a88))
  (.branch 1 (.leaf 0x21cb52c30d06e0288) (.leaf 0xec5e9451da2e7a88))) (.branch 2 (.branch 1
  (.leaf 0x35c69aad6857e7a88) (.leaf 0xa9ef214c803e0a88)) (.branch 1 (.leaf
  0x24db61b7572268a88) (.leaf 0x1731b90ef7766fa88))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2c3b3ae682836fa88) (.leaf 0x8460160922768288)) (.branch 1 (.leaf
  0x16a1ea157171b8288) (.leaf 0x245f92acd125bf288))) (.branch 2 (.branch 1 (.leaf
  0x2316d144a4d0bf288) (.leaf 0x10e95ac2b474b8a88)) (.branch 1 (.leaf 0x2e961a5e9ba530288)
  (.leaf 0x218cc1d88b0137a88)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x7f32230fef437a88)
  (.leaf 0x14ddda895ea030a88)) (.branch 1 (.leaf 0x2de8aa5e946570288) (.leaf
  0x20c301d884c177a88))) (.branch 2 (.branch 1 (.leaf 0x6e25230f13477a88) (.leaf
  0x13a0aa89516070a88)) (.branch 1 (.leaf 0x1355692ace41f8a88) (.leaf
  0x6a641936e15ffa88))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x22aa427b1be0ffa88) (.leaf 0x2d0d79fd0b44f8288)) (.branch 1 (.leaf
  0x168ffb6cf0b454288) (.leaf 0x58a90eae01053a88))) (.branch 2 (.branch 1 (.leaf
  0x286d30295e553a88) (.leaf 0x11075bbb35b154a88)) (.branch 1 (.leaf 0xffce818aa90dca88)
  (.leaf 0x18640a10ac4dba88)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x7f823497f31dba88)
  (.leaf 0x167458cf6f95dc288)) (.branch 1 (.leaf 0xf7ee818a5509ca88) (.leaf
  0xcc40a105049ba88))) (.branch 2 (.branch 1 (.leaf 0x6dcd34970f19ba88) (.leaf
  0x150698cf60559c288)) (.branch 1 (.leaf 0x337338534f8414a88) (.leaf 0x57d43d55f2013288)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2345403d2ad513288) (.leaf
  0xcfb38848a8114288)) (.branch 1 (.leaf 0x2f6b7ec3248010a83) (.leaf 0x99fa545342417283)))
  (.branch 2 (.branch 1 (.leaf 0xa1f26ad41d117283) (.leaf 0x15228e14e18510283)) (.branch 1
  (.leaf 0x2cb96db687c018283) (.leaf 0x325b50f27941f283)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x247bf6e752611f283) (.leaf 0x12411d6142c518a83)) (.branch 1 (.leaf
  0x2cbaed8887d458283) (.leaf 0x2919853127805f283))) (.branch 2 (.branch 1 (.leaf
  0xb4806d952755f283) (.leaf 0x32420d5f42d158a83)) (.branch 1 (.leaf 0x2de8cdc2946450283)
  (.leaf 0x20c5064484c057a83)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x6dea5acf13557a83) (.leaf 0x13a0cd15516150a83)) (.branch 1 (.leaf
  0xe10eca316101c283) (.leaf 0x29b5a41ab6441b283))) (.branch 2 (.branch 1 (.leaf
  0xa4517f2c3b11b283) (.leaf 0x13c80c74d3151ca83)) (.branch 1 (.leaf 0x2c863ce905a014283)
  (.leaf 0x27c476f150413a83)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x259d448760f113a83)
  (.leaf 0x120e3c3ec0a514a83)) (.branch 1 (.leaf 0xc879cd705b454283) (.leaf
  0x28707751151053a83))) (.branch 2 (.branch 1 (.leaf 0xb81f4b960e553a83) (.leaf
  0x120f0c00c0b154a83)) (.branch 1 (.leaf 0x2fa5efa2a6f45ca83) (.leaf 0xffb71b06a05ba83)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x70e14f373555ba83) (.leaf
  0x355dff7563f15c283)) (.branch 1 (.leaf 0x2037940080a78c283) (.leaf 0xf167cb920f38b283)))
  (.branch 2 (.branch 1 (.leaf 0x33f77f5155068b283) (.leaf 0xa7104d745a28ca83)) (.branch 1
  (.leaf 0x284f744a931784283) (.leaf 0x2c587fcc83b383a83)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x17151c24f64683a83) (.leaf 0x24c5d49d561284a83)) (.branch 1 (.leaf
  0x225b44749303c4283) (.leaf 0x2c56fff283a7c3a83))) (.branch 2 (.branch 1 (.leaf
  0x17163c1af652c3a83) (.leaf 0xb5984a35606c4a83)) (.branch 1 (.leaf 0x96497013043cca83)
  (.branch 1 (.leaf 0x2d817fb89017cba83) (.leaf 0x358bbc50e5e2cba83))))))))) (.branch 65
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x273907d6f546cc283) (.leaf 0x2083b55f02c780283)) (.branch 1 (.leaf 0xdb8ced9126387a83)
  (.leaf 0x35b54d31679687a83))) (.branch 2 (.branch 1 (.leaf 0xa9cb588c7c280a83) (.leaf
  0x28d7362aa18788a83)) (.branch 1 (.leaf 0x2c2abe9301d38fa83) (.leaf 0x36e23d7b74268fa83))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x5e366fd648288283) (.leaf 0x22e30614a193c8a83))
  (.branch 1 (.leaf 0xc291ead01c7cfa83) (.leaf 0x16e33d457432cfa83))) (.branch 2 (.branch 1
  (.leaf 0x2b9076c36496c8283) (.leaf 0x983565eb223c0a83)) (.branch 1 (.leaf
  0xf3b7dd8a287c7283) (.leaf 0x14313e30d772c7283))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x275b36897726c0283) (.leaf 0x2c002d0e0013fe33c)) (.branch 1 (.leaf
  0x2656855c6a41f9b3c) (.leaf 0x5f685606542f9b3c))) (.branch 2 (.branch 1 (.leaf
  0x31fbae0dbfe0feb3c) (.leaf 0x1be852a0cb7d7b3c)) (.branch 1 (.leaf 0x34117e47d615d0b3c)
  (.leaf 0x34591e7bd916d0b3c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x29928629b344d733c)
  (.leaf 0x154d6e45e347e7b3c)) (.branch 1 (.leaf 0x3e9d52839e5e0b3c) (.leaf
  0x3c9d51436e6e0b3c))) (.branch 2 (.branch 1 (.leaf 0x14af4d465cb4e733c) (.leaf
  0x578555e5f13ceb3c)) (.branch 1 (.leaf 0x10fdfd0c3541c933c) (.leaf 0x31759d303a42c933c))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2b82265de0e0ce33c) (.leaf
  0x10bb6f6e3283f2b3c)) (.branch 1 (.leaf 0x62fc403e821f5b3c) (.leaf 0x261a343fe722f5b3c)))
  (.branch 2 (.branch 1 (.leaf 0x2d41ac6d8d70f233c) (.leaf 0x20344758ed7dbb3c)) (.branch 1
  (.leaf 0x156b2c27e485dc33c) (.leaf 0x16139c1beb86dc33c)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x97507763124db33c) (.leaf 0x151a1f1a6127ebb3c)) (.branch 1 (.leaf
  0x198d7480b75ec33c) (.leaf 0xb9e7740476ec33c))) (.branch 2 (.branch 1 (.leaf
  0x34e24c19ded4eb33c) (.leaf 0x2698273e6d83c233c)) (.branch 1 (.leaf 0x112a1c53b721c533c)
  (.leaf 0x31429c6fb822c533c))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2b47d43dd270c2b3c) (.leaf 0x309a6f48312612b3c)) (.branch 1 (.leaf 0x2673c425eb8415b3c)
  (.leaf 0x25e40419e48715b3c))) (.branch 2 (.branch 1 (.leaf 0x2d629c4b8ed51233c) (.leaf
  0x1d744538d723bb3c)) (.branch 1 (.leaf 0x15aafc01e7203c33c) (.leaf 0x35c21c3de8233c33c))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2988075032813b33c) (.leaf 0x353b2f3c62820bb3c))
  (.branch 1 (.leaf 0x2149d76e08d00c33c) (.leaf 0x124175207d30c33c))) (.branch 2 (.branch 1
  (.leaf 0x34c14c3fdd710b33c) (.leaf 0x26a757186e262233c)) (.branch 1 (.leaf
  0x10ebfc75b4842533c) (.branch 1 (.leaf 0x11932c49bb872533c) (.leaf
  0xb45241bd1d522b3c)))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x10cd3e17b3461eb3c) (.leaf 0x4ff8645d9141933c)) (.branch 1 (.leaf
  0x4c57679d6171933c) (.leaf 0x2d2fbd140cb51e33c))) (.branch 2 (.branch 1 (.leaf
  0x408a633bfe23733c) (.leaf 0x357d3d5e65403033c)) (.branch 1 (.leaf 0x15f53d626a433033c)
  (.leaf 0x80e3530001137b3c)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1380ed5c50120733c)
  (.leaf 0x18256318ab00033c)) (.branch 1 (.leaf 0x20e0a60d85b30033c) (.leaf
  0x367bce5fefe107b3c))) (.branch 2 (.branch 1 (.leaf 0x2680a647ec462e33c) (.leaf
  0x2c902e15861429b3c)) (.branch 1 (.leaf 0x2cd82e29891729b3c) (.leaf 0x2b4ad54453b52eb3c)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xfc67b4928522b339) (.leaf
  0xa26a31b42002cb39)) (.branch 1 (.leaf 0xb0473274d032cb39) (.leaf 0x2e35884a97a12bb39)))
  (.branch 2 (.branch 1 (.leaf 0x30e50a2a40222b39) (.leaf 0x37ddebcf7ea025b39)) (.branch 1
  (.leaf 0x16a69bf371a325b39) (.leaf 0x89e33a11bf122339)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x12626bf3442612b39) (.leaf 0x28b9e09e9e8415b39)) (.branch 1 (.leaf
  0x83990a2918715b39) (.leaf 0x179a08f0fbd512339))) (.branch 2 (.branch 1 (.leaf
  0x774532778861bb39) (.leaf 0xdc26b7512d41c339)) (.branch 1 (.leaf 0xecb1b491dd71c339) (.leaf
  0x2a922024c7751b339)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x21b7818a8c75b7b39) (.leaf 0x34236ae756d7b0b39)) (.branch 1 (.leaf 0x346b3adb59d4b0b39)
  (.leaf 0x99782893386b7339))) (.branch 2 (.branch 1 (.leaf 0x1092d95eb0d5beb39) (.leaf
  0x2521810cda87b9339)) (.branch 1 (.leaf 0x4b87130d584b9339) (.leaf 0xd6a6a5d0f26be339))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x245c520f50f18eb39) (.leaf 0x117eea5d3aa389339))
  (.branch 1 (.leaf 0x3106ba6135a089339) (.leaf 0x2bbe210cef028e339))) (.branch 2 (.branch 1
  (.leaf 0x14ae59e4dca187339) (.leaf 0xed6289060380339)) (.branch 1 (.leaf 0x14d62b5090080339)
  (.leaf 0x354e7ae7635287b39))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x201a6192800457b39) (.leaf 0x147dfaff5aa650b39)) (.branch 1 (.leaf 0x3405fac355a550b39)
  (.leaf 0x9fac2913ff757339))) (.branch 2 (.branch 1 (.leaf 0x31adf946bca45eb39) (.leaf
  0x4d2a114d6f659339)) (.branch 1 (.leaf 0x5125128d9f559339) (.leaf 0x2c4e4a4503575e339))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x54452175c806eb39) (.leaf 0x3122ea4536d269339))
  (.branch 1 (.leaf 0x316aea7939d169339) (.leaf 0xb8e2114e3736e339))) (.branch 2 (.branch 1
  (.leaf 0x3392e9fcd0d067339) (.leaf 0x17952910a7260339)) (.branch 1 (.leaf
  0x20d9a2ad057160339) (.branch 1 (.leaf 0x1669caff6f2367b39) (.leaf
  0xdf2786e94d3cbb39))))))))))) (.branch 258 (.branch 129 (.branch 64 (.branch 32 (.branch 16
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x7f1803cfe81cc339) (.leaf
  0x26ee3000f182cc339)) (.branch 1 (.leaf 0x3009bb6d2b20cb339) (.leaf 0x88693851883c2339)))
  (.branch 2 (.branch 1 (.leaf 0x1232f8e8c221c5339) (.leaf 0x1339d8d4cd22c5339)) (.branch 1
  (.leaf 0x31ec086a770c2b39) (.leaf 0x174e68d4f8a7f2339)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2ec53b92205f5339) (.leaf 0x35e13852d06f5339)) (.branch 1 (.leaf
  0x12ae3bd74754f2b39) (.leaf 0x2a505000c407fb339))) (.branch 2 (.branch 1 (.leaf
  0x30577852ae55fcb39) (.leaf 0xf1e586ea156fcb39)) (.branch 1 (.leaf 0x7ba23037bf4fbb39)
  (.leaf 0x23ce2346380080a37))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x1000f99faac48b237) (.leaf 0x34ec7a77df318b237)) (.branch 1 (.leaf 0xbf45391fd0580237)
  (.leaf 0x311439f2363085237))) (.branch 2 (.branch 1 (.leaf 0x26da01414048e237) (.leaf
  0x25b053fc61f18e237)) (.branch 1 (.leaf 0x16cc6925f33585a37) (.leaf 0x4c4c2a3d614b5237))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x36e19b45f420be237) (.leaf 0x2c2a18ad81d5be237))
  (.branch 1 (.leaf 0x84ed2741311b5a37) (.leaf 0x15d33b2868d4b0237))) (.branch 2 (.branch 1
  (.leaf 0x2792e1f1fa10bba37) (.leaf 0x227c2198fe5bba37)) (.branch 1 (.leaf
  0x304b6bffadd1b0a37) (.leaf 0x21336060086086237)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x2ff679862a548d237) (.leaf 0x34f61a6e5fa18d237)) (.branch 1
  (.leaf 0xb0b70b7cd6586a37) (.leaf 0x111eb9ebb6a083237))) (.branch 2 (.branch 1 (.leaf
  0x23105332246488a37) (.leaf 0x46950da519188a37)) (.branch 1 (.leaf 0x16d6193c73a583a37)
  (.leaf 0x24cff2ba5684b3237)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x12657863c440b8a37)
  (.leaf 0x10a87b8bb1b5b8a37)) (.branch 1 (.leaf 0x85a226d9381b3a37) (.leaf
  0x1450380e58b4b6a37))) (.branch 2 (.branch 1 (.leaf 0x7a051e87a80bda37) (.leaf
  0x21932000f75bda37)) (.branch 1 (.leaf 0x2ec7f8d99db1b6237) (.leaf 0x18e207a0b0626237)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2fdb799c29322d237) (.leaf
  0x14b17a745cc72d237)) (.branch 1 (.leaf 0xb17f0adce0326a37) (.leaf 0x110979f1b5c623237)))
  (.branch 2 (.branch 1 (.leaf 0x31d5328270228a37) (.leaf 0x48450c052f728a37)) (.branch 1
  (.leaf 0x3691e92670c323a37) (.leaf 0x4bf72a055e213237)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x12aa1879c72618a37) (.leaf 0x30c37b91b2d318a37)) (.branch 1 (.leaf
  0x82d927790e713a37) (.leaf 0x149a98145bd216a37))) (.branch 2 (.branch 1 (.leaf
  0x278f51f279e61da37) (.leaf 0x1b2021a0c131da37)) (.branch 1 (.leaf 0xee368c39ed716237)
  (.leaf 0x219ad0638b9620237))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2e5e7aba19522ba37) (.leaf 0x162ef9526ca72ba37)) (.branch 1 (.leaf
  0xb20c0b44e9320a37) (.leaf 0x2c859ad785a625a37))) (.branch 2 (.branch 1 (.leaf
  0x2323a331a7922ea37) (.leaf 0x47ae0d9d2672ea37)) (.branch 1 (.leaf 0x120d9a0040a325237)
  (.leaf 0x25fe0186658215a37)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x32b8486047b61ea37)
  (.leaf 0x30b5cb8832431ea37)) (.branch 1 (.leaf 0x28c99151a08715237) (.leaf
  0x348dc80ddb4210a37))) (.branch 2 (.branch 1 (.leaf 0x2431e2d449861b237) (.leaf
  0x3f1913c3c731b237)) (.branch 1 (.leaf 0xed5c8da1e4710237) (.leaf 0x2cfaadba8a8725a32)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2a857451be6ce232) (.leaf
  0x26a554ad6e13ce232)) (.branch 1 (.leaf 0x1372ad6d4f8225232) (.leaf 0x2129d4e707e6e0232)))
  (.branch 2 (.branch 1 (.leaf 0x2f994d2726770b232) (.leaf 0x33d39ecf53820b232)) (.branch 1
  (.leaf 0x2a377430c2e3e0a32) (.leaf 0x15c12f88e816d0232)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x242f2648c9873b232) (.leaf 0x3efa5a0bc723b232)) (.branch 1 (.leaf
  0x10392f5f2d13d0a32) (.leaf 0x24b805ead58715232))) (.branch 2 (.branch 1 (.leaf
  0x1274af1544e6fea32) (.leaf 0x30992cfd3113fea32)) (.branch 1 (.leaf 0x2827953d108215a32)
  (.leaf 0x315deebab942c3232)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2298a77a98d328232) (.leaf 0x26925492ed2628232)) (.branch 1 (.leaf
  0x17a51e6d7c47c3a32) (.leaf 0xc8a4d884d306232))) (.branch 2 (.branch 1 (.leaf
  0xe074e2715b2eda32) (.leaf 0x15051dcf6047eda32)) (.branch 1 (.leaf 0x2a21840f41d606a32)
  (.leaf 0x360aefb76b2336232)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x279e5548fa42dda32)
  (.leaf 0x21ec6a08fb7dda32)) (.branch 1 (.leaf 0x10527f60ae2636a32) (.leaf
  0x60df6eae642f3a32))) (.branch 2 (.branch 1 (.leaf 0x32baff2ac7d318a32) (.leaf
  0x30b29cc2b22618a32)) (.branch 1 (.leaf 0x8f6d63d2347f3232) (.leaf 0x11727ea0ba2463232)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2a3a7609bb588232) (.leaf
  0x26ae5488ee4088232)) (.branch 1 (.leaf 0x17eabe777f2163a32) (.leaf 0x211ee4c287b5a6232)))
  (.branch 2 (.branch 1 (.leaf 0x2e224e3d16d44da32) (.leaf 0x154a7dd563214da32)) (.branch 1
  (.leaf 0x2a31f41542b0a6a32) (.leaf 0x35c51fad684596232)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x277ea552f9247da32) (.leaf 0x21c906ba8cd17da32)) (.branch 1 (.leaf
  0x303dbf7aad4096a32) (.leaf 0x5f586f0e52453a32))) (.branch 2 (.branch 1 (.leaf
  0x326f9f30c4b5b8a32) (.leaf 0x109d9cd8b140b8a32)) (.branch 1 (.leaf 0x28c09627202153232)
  (.branch 1 (.leaf 0x11596e9f391185232) (.leaf 0x232fa460a8706ea32))))))))) (.branch 64
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x55e5788dd856ea32) (.leaf 0x37a13e48fc1485a32)) (.branch 1 (.leaf 0x23af27c2b47040a32)
  (.leaf 0x2e0bce0295e1aba32))) (.branch 2 (.branch 1 (.leaf 0x35011deae014aba32) (.leaf
  0x2bc4c715717540232)) (.branch 1 (.leaf 0x1493ecad5b8070a32) (.leaf 0x2795556d7a119ba32))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x22a06850fe49ba32) (.leaf 0xedbbc7a9e8570232))
  (.branch 1 (.leaf 0x60376cf6611b5a32) (.leaf 0x37312c30f7705e232))) (.branch 2 (.branch 1
  (.leaf 0xc3aafd882855e232) (.leaf 0x8f1e618a314b5232)) (.branch 1 (.leaf
  0x33f3bda3d4e2cb38d) (.leaf 0xff8cc0daa6750b8d))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2f80cc31a56450b8d) (.leaf 0x16080ea06b11cbb8d)) (.branch 1 (.leaf
  0x2b8d072a63755fb8d) (.leaf 0x235c05bbad00c4b8d))) (.branch 2 (.branch 1 (.leaf
  0x22ebc587a203c4b8d) (.leaf 0x25434429dc865f38d)) (.branch 1 (.leaf 0x25d0f71463611fb8d)
  (.leaf 0x9503585ad1484b8d)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x8dff5b9a21784b8d)
  (.leaf 0xb6ff417dc921f38d)) (.branch 1 (.leaf 0x355faea264068bb8d) (.leaf
  0xe7baf0c1a831038d))) (.branch 2 (.branch 1 (.leaf 0x2e03af3015801038d) (.leaf
  0x349e2da1dbf58b38d)) (.branch 1 (.leaf 0x6f5d62672355db8d) (.leaf 0x29e5e4b7bc40c6b8d))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2994d48bb343c6b8d) (.leaf
  0x2b162525cdc65d38d)) (.branch 1 (.leaf 0x36fe3f907552c9b8d) (.leaf 0xd1b6e3e0bd75238d)))
  (.branch 2 (.branch 1 (.leaf 0x2c729e0204d45238d) (.leaf 0x32fe1c93caa1c938d)) (.branch 1
  (.leaf 0x36fd2fae754689b8d) (.leaf 0xd19ee000bc31238d)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2c712e3c04c01238d) (.leaf 0x12ff0cadcab58938d)) (.branch 1 (.leaf
  0xa34d527c2d11d38d) (.leaf 0x1be17b60ca48638d))) (.branch 2 (.branch 1 (.leaf
  0x9fd78a03a78638d) (.leaf 0x7d5a6247d221db8d)) (.branch 1 (.leaf 0x26e5a63c7153fdb8d) (.leaf
  0x29f3e4adbf2666b8d))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x9621491b02566b8d) (.leaf 0x2b24d53fcea0fd38d)) (.branch 1 (.leaf 0x17133f8a763469b8d)
  (.leaf 0xccfae2408b1f238d))) (.branch 2 (.branch 1 (.leaf 0xcb83e1807b2f238d) (.leaf
  0x32e92c89c9c76938d)) (.branch 1 (.leaf 0x17121fb4762029b8d) (.leaf 0xcce1e1a08a5b238d))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0xcb6be2607a6b238d) (.leaf 0x12ea0cb7c9d32938d))
  (.branch 1 (.leaf 0x2a1c253dc1b7bd38d) (.leaf 0x22427ac0fc22638d))) (.branch 2 (.branch 1
  (.leaf 0x2040379000c12638d) (.leaf 0x7ebd63e7e44bdb8d)) (.branch 1 (.leaf
  0x35b13e8667746bb8d) (.leaf 0x2e6e6f2819f1f038d))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e263f1416f2f038d) (.leaf 0x344a8d85d8876b38d))
  (.branch 1 (.leaf 0x2b3ff40fd0e3ff38d) (.leaf 0x2c3f69e1e966438d))) (.branch 2 (.branch 1
  (.leaf 0x224606a211956438d) (.leaf 0x6b8f70c6f10ffb8d)) (.branch 1 (.leaf
  0x45b4431d0f7bf38d) (.leaf 0x8b7c6a01e822438d)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x283a369c11812438d) (.leaf 0xbbd07326f04bfb8d)) (.branch 1 (.leaf 0x14354d87d7902b38d)
  (.leaf 0xfd96c29a915b0b8d))) (.branch 2 (.branch 1 (.leaf 0xf913c15a616b0b8d) (.leaf
  0x35c8ce8468632bb8d)) (.branch 1 (.leaf 0x30d29b15b3836f386) (.leaf 0x535e2185bb164b86)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x4a8622454b264b86) (.leaf
  0xd2918160c706fb86)) (.branch 1 (.leaf 0x1619193e6bc7ebb86) (.leaf 0x39dd30c3305e0b86)))
  (.branch 2 (.branch 1 (.leaf 0x23ebe3303c06e0b86) (.leaf 0x13e3aa3dd434eb386)) (.branch 1
  (.leaf 0x155fc93e6407abb86) (.leaf 0x3f8d30c3cc5a0b86)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x23a9e33033c6a0b86) (.leaf 0x149e4a3ddbf4ab386)) (.branch 1 (.leaf
  0xd2f282a0cb32fb86) (.leaf 0x5e31127e48124386))) (.branch 2 (.branch 1 (.leaf
  0x673911beb8224386) (.leaf 0x30ccab29b3402f386)) (.branch 1 (.leaf 0xc5c483383e369b86)
  (.leaf 0x25279201db2162b86)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x49f123dd42262b86) (.leaf 0x11a0cb303c1069386)) (.branch 1 (.leaf
  0x160f5927eb57edb86) (.leaf 0x209a102a0365e6386))) (.branch 2 (.branch 1 (.leaf
  0x21b4d0160c66e6386) (.leaf 0x33eeda2454a4ed386)) (.branch 1 (.leaf 0x156ca927e497adb86)
  (.leaf 0x21bd102a0ca5a6386)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x20a1d01603a6a6386)
  (.leaf 0x34901a245b64ad386)) (.branch 1 (.leaf 0x31b2fb0c3cd329386) (.leaf
  0x25dc613e641122386))) (.branch 2 (.branch 1 (.leaf 0x669e1026b1222386) (.leaf
  0x2c4a780f832029b86)) (.branch 1 (.leaf 0x2c0b18298085c9b86) (.leaf 0x24eed21bd847c2b86)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x24e26227d744c2b86) (.leaf
  0x11f1ab2a3f76c9386)) (.branch 1 (.leaf 0x35c3993de8314db86) (.leaf 0x200ab030000346386)))
  (.branch 2 (.branch 1 (.leaf 0x20e100c0f0046386) (.leaf 0x34392a3e57c24d386)) (.branch 1
  (.leaf 0x35be093de7f10db86) (.leaf 0x222620300fc306386)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x3f700c00c006386) (.leaf 0x343f8a3e58020d386)) (.branch 1 (.leaf
  0x11f79b163fb589386) (.leaf 0x26216124677782386))) (.branch 2 (.branch 1 (.leaf
  0x26359118687482386) (.leaf 0x2c052815804689b86)) (.branch 1 (.leaf 0xc00b8300015cfb86)
  (.branch 1 (.leaf 0x262ed13de827c4386) (.leaf 0x61a6101e724c4386)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x11fc3b33bfe6cf386) (.leaf 0x34469a1bd8514b386)) (.branch 1 (.leaf 0x2032b029809340386)
  (.leaf 0x221ae0158f9040386))) (.branch 2 (.branch 1 (.leaf 0x15b6291867a24bb86) (.leaf
  0x34352a1bd7910b386)) (.branch 1 (.leaf 0x2212d0298f5300386) (.leaf 0x2026d015805000386))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x15c8a91868620bb86) (.leaf 0x31ea0b0fbf258f386))
  (.branch 1 (.leaf 0x24d96202571784b86) (.leaf 0x4ed923e581484b86))) (.branch 2 (.branch 1
  (.leaf 0x2c12880c00d68fb86) (.leaf 0x24ec6262581584b82)) (.branch 1 (.leaf
  0x254060185c661f382) (.leaf 0x254a401a5cb11f382))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2ba2115fe83284382) (.leaf 0x2e24a8ea16e690382)) (.branch 1 (.leaf
  0x2f38a9afa2650b382) (.leaf 0x2f4029ada2b20b382))) (.branch 2 (.branch 1 (.leaf
  0x2fa1abd7a6c190b82) (.leaf 0x2e5ac8ea1926d0382)) (.branch 1 (.leaf 0x3045e9afada54b382)
  (.leaf 0x304159adad724b382)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2fd7cbd7a901d0b82)
  (.leaf 0x2617915de725c4382)) (.branch 1 (.leaf 0x5cab327e3565fb82) (.leaf
  0x25d49325e3815fb82))) (.branch 2 (.branch 1 (.leaf 0xb5ab2605702c4b82) (.leaf
  0x17e1e9e7fec212382)) (.branch 1 (.leaf 0x12f4e8a24a4189382) (.leaf
  0x32fcc8a04a9689382)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x33644ada4ee512b82) (.leaf 0x2041a05000c106382)) (.branch 1 (.leaf 0xc2422a04b29db82)
  (.leaf 0xb5b22804659db82))) (.branch 2 (.branch 1 (.leaf 0x296e236db0e606b82) (.leaf
  0x220be0500f0146382)) (.branch 1 (.leaf 0x19a022a0b72ddb82) (.leaf 0x19f32280ba5ddb82))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x29f4136dbf2646b82) (.leaf 0x322e6ad841f252b82))
  (.branch 1 (.leaf 0x1701fb9df571c9b82) (.leaf 0x1705db9ff5a6c9b82))) (.branch 2 (.branch 1
  (.leaf 0x36aaf9e5f1d552382) (.leaf 0x37c679fdfda4b2382)) (.branch 1 (.leaf
  0x12d9e8b8492729382) (.leaf 0x12edf8ba49f029382))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x3343bac04d83b2b82) (.leaf 0xa0204a03a7a6382)) (.branch 1 (.leaf
  0x125c23007d43db82) (.leaf 0x210af23207033db82))) (.branch 2 (.branch 1 (.leaf
  0x29991377b380a6b82) (.leaf 0x1b6204a0c67e6382)) (.branch 1 (.leaf 0x131b23008147db82)
  (.leaf 0x2146423208c37db82)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x29e61377bc40e6b82)
  (.leaf 0x123ccac24294f2b82)) (.branch 1 (.leaf 0x1710cb87f61769b82) (.leaf
  0x3720db85f6c069b82))) (.branch 2 (.branch 1 (.leaf 0x36c039fff2b3f2382) (.leaf
  0x26766147eb8324382)) (.branch 1 (.leaf 0x26c8933deff0bfb82) (.leaf
  0x26bab33fef27bfb82))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0x2b6ae27a5ba424b82) (.leaf 0xf826bcfa57030b82)) (.branch 1 (.leaf
  0xdae4a8a11f3abb82) (.leaf 0xd9aca881124abb82))) (.branch 2 (.branch 1 (.leaf
  0xdff38f2155730382) (.leaf 0x10006bcfaab070b82)) (.branch 1 (.leaf 0xed36a8a1e33ebb82)
  (.leaf 0xee3da881ee4ebb82)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xe7d38f21a9770382)
  (.leaf 0x24a9927854b364b82)) (.branch 1 (.leaf 0x45a400250c0ff382) (.leaf
  0x244c60005017ff382))) (.branch 2 (.branch 1 (.leaf 0xb924145e49464382) (.leaf
  0x2374d4ea30a020b89)) (.branch 1 (.leaf 0xf38ce33a2642b389) (.leaf 0xf404e31a2b32b389)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x81827d7808720389) (.leaf
  0x837c6c0118024389)) (.branch 1 (.leaf 0x10d71f2633b42f389) (.leaf 0x10cf9f2433632f389)))
  (.branch 2 (.branch 1 (.leaf 0x22e7c5fda1a724b89) (.leaf 0x243f6fe119464389)) (.branch 1
  (.leaf 0x10d5af1833a06f389) (.leaf 0x10d12f1a33776f389)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x8dbf5c3a1b364b89) (.leaf 0x81647eb804460389)) (.branch 1 (.leaf 0xdbb7d3212806bb89)
  (.leaf 0x2db6cd3012576bb89))) (.branch 2 (.branch 1 (.leaf 0x237114d6306360b89) (.leaf
  0x40e7cc00c026389)) (.branch 1 (.leaf 0xf465e2a22f42d389) (.leaf 0xf32de2822232d389))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x96c24f1b0e726b89) (.leaf
  0x830f6d9911022389)) (.branch 1 (.leaf 0xc5afc0003d429b89) (.leaf 0x2c474c02030329b89)))
  (.branch 2 (.branch 1 (.leaf 0x22e0f5e4213722b89) (.leaf 0x223cc6e7910462389)) (.branch 1
  (.leaf 0xc597c3e03c069b89) (.leaf 0x2c48cc3c031769b89)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x28d4c5da212362b89) (.leaf 0x295fe4cdb02466b89)) (.branch 1 (.leaf
  0x2db0fd2b92106db89) (.leaf 0xdc14d2992c76db89))) (.branch 2 (.branch 1 (.leaf
  0x200d47f0000366389) (.leaf 0x20a227d603a686389)) (.branch 1 (.leaf 0xf24ce3021928d389)
  (.leaf 0x2f1d7e3221458d389))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x99a14ebb38186b89) (.leaf 0x284bf6c3927682389)) (.branch 1 (.leaf 0xc0fac1a00b289b89)
  (.leaf 0xc082c18006589b89))) (.branch 2 (.branch 1 (.leaf 0x22eef5fe225182b89) (.leaf
  0x257c6fd9262c2389)) (.branch 1 (.leaf 0xc0e1c2400a6c9b89) (.leaf 0xc099c260071c9b89))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x28e2c5c02245c2b89) (.leaf 0x99624d7b342c6b89))
  (.branch 1 (.leaf 0x2da20d319176cdb89) (.leaf 0x2da68d3391a1cdb89))) (.branch 2 (.branch 1
  (.leaf 0x2099e7ea0365c6389) (.leaf 0x208ed7cf833680389)) (.branch 1 (.leaf
  0x2dae2d1611f28bb89) (.branch 1 (.leaf 0x2d9aad1411258bb89) (.leaf
  0x98ee4f2331180b89))))))))) (.branch 65 (.branch 32 (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x28e205e5a21684b89) (.leaf 0xc020c0380228fb89)) (.branch 1
  (.leaf 0xc158c0180f58fb89) (.leaf 0x250f6d8123184389))) (.branch 2 (.branch 1 (.leaf
  0x2ee35dba202c4b89) (.leaf 0x2c03bc3d8036cfb89)) (.branch 1 (.leaf 0x2c143c3f80e1cfb89)
  (.leaf 0x844c6e61225c4389)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x299ad4ce33d2c0b89)
  (.leaf 0xf18fe17a116cb389)) (.branch 1 (.leaf 0x2f294e15a1c1cb389) (.leaf
  0xa717f383f5c0389))) (.branch 2 (.branch 1 (.leaf 0x2c19afa28121be236) (.leaf
  0x63f76af6913b5a36)) (.branch 1 (.leaf 0x261d5791332b5a36) (.leaf 0x131d2f4b4bf0bea36)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x227f6d90fe59ba36) (.leaf
  0x142abceb572790a36)) (.branch 1 (.leaf 0x3037ef3d2d0690a36) (.leaf 0x2a695630c5349b236)))
  (.branch 2 (.branch 1 (.leaf 0x35017db6e015aba36) (.leaf 0x3d72784b8d7a0a36)) (.branch 1
  (.leaf 0x2414a452c2f6a0a36) (.leaf 0x3000cd5f2ac4ab236)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x563a7f2de218ea36) (.leaf 0x11113eff361385236)) (.branch 1 (.leaf
  0x13246d294c3285236) (.leaf 0x86e671b14f08e236))) (.branch 2 (.branch 1 (.leaf
  0x109dfc84b141b8a36) (.leaf 0x64c06b6e983b3a36)) (.branch 1 (.leaf 0x267256093a2b3a36)
  (.leaf 0x3794cc6d7b90b8236)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x21906c08f759da36) (.leaf 0x35adbfcd674796236)) (.branch 1 (.leaf
  0xec04c1b1d6696236) (.leaf 0x2a6fa62945a49d236))) (.branch 2 (.branch 1 (.leaf
  0x150b2daf6085ada36) (.leaf 0x213ea4a288b7a6236)) (.branch 1 (.leaf 0x6fc0774f296a6236)
  (.leaf 0xff64d46aa54ad236)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x26aca4d4ee4188236)
  (.leaf 0x311bbee6b68383236)) (.branch 1 (.leaf 0x332e2d30cca283236) (.leaf
  0x2907943d249088a36))) (.branch 2 (.branch 1 (.leaf 0x30b2fc9eb22718a36) (.leaf
  0x66406aceae513a36)) (.branch 1 (.leaf 0x223a557a90c413a36) (.leaf 0x3755ac7778f618236)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1b236da8c133da36) (.leaf
  0x15622fd7642136236)) (.branch 1 (.leaf 0xecfec011e0036236) (.leaf 0xa86a63346c23d236)))
  (.branch 2 (.branch 1 (.leaf 0x355c4db563e30da36) (.leaf 0x21a324b88bd106236)) (.branch 1
  (.leaf 0x26f0076ef1f006236) (.leaf 0xfdb4d5ca9320d236)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x268fa4ceed2728236) (.leaf 0x110c4efcb5e523236)) (.branch 1 (.leaf
  0x3379ed2acfc423236) (.leaf 0x91c942727f628a36))) (.branch 2 (.branch 1 (.leaf
  0x30c04c8732b71ea36) (.leaf 0x521f58ada8515236)) (.branch 1 (.leaf 0x22d6565ca0a415236)
  (.branch 1 (.leaf 0x3748cc6ef8661e236) (.leaf 0x3f255fcbc733b236)))))))) (.branch 32
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x15704fcee4b130236) (.leaf
  0xedd4c189e9030236)) (.branch 1 (.leaf 0xbd7451576a23ba36) (.leaf 0x33d3fe9353830b236)))
  (.branch 2 (.branch 1 (.leaf 0x195d4a10b4100236) (.leaf 0x6e77777716000236)) (.branch 1
  (.leaf 0xe5e4e7a99520ba36) (.leaf 0x69d54d76db72e236)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xc82adda858525a36) (.leaf 0x37f5ae0cffa425a36)) (.branch 1 (.leaf
  0x2914643ea7662ea36) (.leaf 0x3f061603c721b233))) (.branch 2 (.branch 1 (.leaf
  0x143ca84bd7e5f0a33) (.leaf 0x1049ab9dadc4f0a33)) (.branch 1 (.leaf 0xbd9d189f6a31ba33)
  (.leaf 0x30acabf231e7fea33))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x65bf1e66a8015a33) (.leaf 0x2234523010a115a33)) (.branch 1 (.leaf 0x378c2b1bfb36fe233)
  (.leaf 0x246ae0a3d1c3cea33))) (.branch 2 (.branch 1 (.leaf 0xcfd9ab78aa425a33) (.leaf
  0x368a9961f08525a33)) (.branch 1 (.leaf 0x288f904a1b12ce233) (.leaf 0x162e990e6ca62ba33))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x210ed0258731c0233) (.leaf 0x27d0c3f3fd10c0233))
  (.branch 1 (.leaf 0xf9979e7a6772b233) (.leaf 0x21ef2600fb7fda33))) (.branch 2 (.branch 1
  (.leaf 0x33f3687454d016a33) (.leaf 0x3065cba22ef116a33)) (.branch 1 (.leaf
  0xa6da289c566fd233) (.leaf 0x30c31bcdb2d218a33)))))) (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x250a02e65945f3233) (.leaf 0x309d1302364f3233)) (.branch 1
  (.leaf 0x373f4b24780318233) (.leaf 0x485a09c52f628a33))) (.branch 2 (.branch 1 (.leaf
  0x1160e9b7b961c3233) (.leaf 0x324d2a61c340c3233)) (.branch 1 (.leaf 0x8816075982728233)
  (.leaf 0x34f02a0e5f63cd233)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x20ad601a040426233)
  (.leaf 0x27e8f3cc7e2526233)) (.branch 1 (.leaf 0x2e077ae795b2cda33) (.leaf
  0x21c9327a0cd15da33))) (.branch 2 (.branch 1 (.leaf 0x1437a86e57b6b6a33) (.leaf
  0x30453bb82d97b6a33)) (.branch 1 (.leaf 0xa775293c6005d233) (.leaf 0x10a81bd7b1b4b8a33)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x518f2fc5a2353233) (.leaf
  0x2cd512a200253233)) (.branch 1 (.leaf 0x37902b3e7b65b8233) (.leaf 0x469a086519088a33)))
  (.branch 2 (.branch 1 (.leaf 0x116f49adba0763233) (.leaf 0x1202ba7bc02663233)) (.branch 1
  (.leaf 0x2894606f9b4188233) (.leaf 0x349f4a145c056d233)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2119e000076286233) (.leaf 0x7da03d67d4386233)) (.branch 1 (.leaf
  0xe227afd96d46da33) (.leaf 0x22a32458fe4bba33))) (.branch 2 (.branch 1 (.leaf
  0x356a6b6e647350233) (.leaf 0xed738b81e5250233)) (.branch 1 (.leaf 0x2a66e2ac4535bb233)
  (.branch 1 (.leaf 0xc3918d782715e233) (.leaf 0x500c2c3d916b5233)))))))))))) (.branch 517
  (.branch 258 (.branch 129 (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch
  2 (.branch 1 (.leaf 0x2fee115a337b5233) (.leaf 0x32cd983e48a05ea33)) (.branch 1 (.leaf
  0x25b9a38662556e233) (.leaf 0x315c6992393285233))) (.branch 2 (.branch 1 (.leaf
  0x32493a44431385233) (.leaf 0x928636fa8846ea33)) (.branch 1 (.leaf 0x34ec1a2bdf308b233)
  (.leaf 0x23b6230034a760a33)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x44460d64e8660a33)
  (.leaf 0xe0bfac215e18ba33)) (.branch 1 (.leaf 0x10456b142d95b6a31) (.leaf
  0x29eda1ebbcf45d231))) (.branch 2 (.branch 1 (.leaf 0x2ab35203c9015d231) (.leaf
  0x15cc0bc3e890b6231)) (.branch 1 (.leaf 0x22cda186200053231) (.leaf 0xc2438460191b8231)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x16e89bae7464b8231) (.leaf
  0x2b943151e50553a31)) (.branch 1 (.leaf 0x3202ead7c02463231) (.leaf 0x2b85e317e1b588231)))
  (.branch 2 (.branch 1 (.leaf 0x86590ff944088231) (.leaf 0xc798a00052163a31)) (.branch 1
  (.leaf 0x27d6f37a7d4186231) (.leaf 0x3621b985ec206da31)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2e6a7a6d99d56da31) (.leaf 0x29c623adb84486a31)) (.branch 1 (.leaf
  0x20c1a36204b500231) (.leaf 0x2f79caa22524eb231))) (.branch 2 (.branch 1 (.leaf
  0x1393194a50d1eb231) (.leaf 0xa1af3b5c1b000a31)) (.branch 1 (.leaf 0x116b1acfb9d0e5231)
  (.leaf 0x335a03028b10ea31)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x55953d85d440ea31) (.leaf 0x17b31a187cd5e5a31)) (.branch 1 (.leaf
  0x510519e59f4d5231) (.leaf 0x32cc4b61c8953ea31))) (.branch 2 (.branch 1 (.leaf
  0x11bff889bd603ea31) (.leaf 0x28ae21499cf1d5a31)) (.branch 1 (.leaf 0x33e7fb0c546130a31)
  (.leaf 0x74212cc75f0dba31)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x200951240005dba31)
  (.leaf 0xd9ffbdb916430231)) (.branch 1 (.leaf 0x212b63460807a0231) (.leaf
  0x2fe47a8629964b231))) (.branch 2 (.branch 1 (.leaf 0x34a8f96e5c634b231) (.leaf
  0xb02f391cd02a0a31)) (.branch 1 (.leaf 0x31005aebb56245231) (.leaf 0x30c50142403aea31)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x247153fc51f6aea31) (.leaf
  0x36886a3c706745a31)) (.branch 1 (.leaf 0x24b601ba554675231) (.leaf 0x32629b45c4279ea31)))
  (.branch 2 (.branch 1 (.leaf 0x30ab78adb1d29ea31) (.leaf 0x825916d904375a31)) (.branch 1
  (.leaf 0x1452db2858d390a31) (.leaf 0x2785d2e879427ba31)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x21c1c1000cb77ba31) (.leaf 0x2ecaebff9dd690231)) (.branch 1 (.leaf
  0x2daa580f91d716231) (.leaf 0x203da2f000b6fda31))) (.branch 2 (.branch 1 (.leaf
  0x273751187543fda31) (.leaf 0x13f338d854d216a31)) (.branch 1 (.leaf 0x28a6229d9c42f3a31)
  (.leaf 0x11ca6b5dbdd318a31))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x12c298b5c82618a31) (.leaf 0x506f24a5947f3231)) (.branch 1 (.leaf
  0x37a7d9cc7c66c3a31) (.leaf 0x2561d00c5df728a31))) (.branch 2 (.branch 1 (.leaf
  0x32da3e4280228a31) (.leaf 0x3160b91bb963c3231)) (.branch 1 (.leaf 0x2a143061c10326a31)
  (.leaf 0x1387ea9e5062cd231)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xf8479762597cd231)
  (.leaf 0xad90b6040626231)) (.branch 1 (.leaf 0x238a5d690c613a34) (.leaf
  0x2c2ebf0f020218234))) (.branch 2 (.branch 1 (.leaf 0x373e7ce777f718234) (.leaf
  0x2b54c50155c313234)) (.branch 1 (.leaf 0x2ecfbcad1e0236234) (.leaf 0x9e0a54b3c363d234)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2ac2a6a349c33d234) (.leaf
  0x34868c7adb0736a34)) (.branch 1 (.leaf 0x6ef07c2f1f206234) (.leaf 0x33d8be24d3c60d234)))
  (.branch 2 (.branch 1 (.leaf 0x2f934dcca6330d234) (.leaf 0x9ab171534f706a34)) (.branch 1
  (.leaf 0x1379bd86cfc623234) (.leaf 0xb73175f5d0228a34)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x92b94b728f728a34) (.leaf 0xd008d510ac323a34)) (.branch 1 (.leaf
  0x31756d86ba4345234) (.leaf 0x228fa46098774e234))) (.branch 2 (.branch 1 (.leaf
  0x6972788ed824e234) (.leaf 0x37ed5d517f4645a34)) (.branch 1 (.leaf 0x20b8a7c2847760234)
  (.leaf 0x2e1f4d1b16b36ba34)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x154d9ef363466ba34) (.leaf 0x2a170715417260a34)) (.branch 1 (.leaf
  0x16136cad6b8750234) (.leaf 0x2783a674f9435ba34))) (.branch 2 (.branch 1 (.leaf
  0x21c1059c8cb65ba34) (.leaf 0x105b5c7aae8250a34)) (.branch 1 (.leaf 0x25f905d6e54375a34)
  (.leaf 0x32b27c30c7777ea34)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x10bb9fd8b2827ea34)
  (.leaf 0x8c49501204675234)) (.branch 1 (.leaf 0x31267da2b6f1e5234) (.leaf
  0x278a44494c5ee234))) (.branch 2 (.branch 1 (.leaf 0x5a257ace130ee234) (.leaf
  0x36de7d7573f4e5a34)) (.branch 1 (.leaf 0x14497e688c5c0234) (.leaf 0xe6efd3f1a01cba34)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x167e7ed76ff4cba34) (.leaf
  0xb15f7314dc0c0a34)) (.branch 1 (.leaf 0x35ab4c896735f0234) (.leaf 0x73f4650f5f1fba34)))
  (.branch 2 (.branch 1 (.leaf 0x2017c5b88004fba34) (.leaf 0x2f334c5ea230f0a34)) (.branch 1
  (.leaf 0x65105f2e9f1d5a34) (.leaf 0x3318fc14cbc5dea34)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x31d34ffcbe30dea34) (.leaf 0x294b15252cf4d5234)) (.branch 1 (.leaf
  0x2946d6cd2c84b3234) (.leaf 0x11d4ec14be40b8a34))) (.branch 2 (.branch 1 (.leaf
  0x13187ffccbb5b8a34) (.leaf 0x264df61ae981b3a34)) (.branch 1 (.leaf 0x2f34dfb6a24096a34)
  (.branch 1 (.leaf 0x202ea65080749da34) (.leaf 0x73e55b8f5819da34))))))))) (.branch 64
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x15adef61674596234) (.leaf 0x2b1104d94db0a6a34)) (.branch 1 (.leaf 0x3672ed3f6f84ada34)
  (.leaf 0x2e794ed71a71ada34))) (.branch 2 (.branch 1 (.leaf 0x140a40e88b5a6234) (.leaf
  0x36d2de9d738483a34)) (.branch 1 (.leaf 0x25a34444e14088234) (.leaf 0x2274a7ac94b588234))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x111bee4ab68183234) (.leaf 0x14973d4a5bb18d38b))
  (.branch 1 (.leaf 0x2998e447b38386b8b) (.leaf 0x29e9d47bbc8086b8b))) (.branch 2 (.branch 1
  (.leaf 0x15648e49e4428db8b) (.leaf 0x377c3f607a9189b8b)) (.branch 1 (.leaf
  0x2f0f552225382b8b) (.leaf 0x2360356e2d5082b8b))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x32802c63c5628938b) (.leaf 0x377b1f5e7a85c9b8b)) (.branch 1 (.leaf
  0x8e4c56c2247c2b8b) (.leaf 0x295405502d44c2b8b))) (.branch 2 (.branch 1 (.leaf
  0x12810c5dc576c938b) (.leaf 0x360f0e4beb55cdb8b)) (.branch 1 (.leaf 0x9917460367c638b)
  (.leaf 0x1b5d77a0c64c638b)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x13ee8d4854a6cd38b)
  (.leaf 0x26e1251a7134dbb8b)) (.branch 1 (.leaf 0x2fee7f2829f6d0b8b) (.leaf
  0x2fa61f1426f5d0b8b))) (.branch 2 (.branch 1 (.leaf 0xb28d619cec7db38b) (.leaf
  0x2b7ff40fe0e4dfb8b)) (.branch 1 (.leaf 0xcd2ad0208d6d438b) (.leaf 0x2cbb1d3e07d5d438b))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x578f70c5f17df38b) (.leaf
  0x59b4431e0f09fb8b)) (.branch 1 (.leaf 0xcd11d3c08c29438b) (.leaf 0x2cb99d0007c19438b)))
  (.branch 2 (.branch 1 (.leaf 0xb7d07325f039f38b) (.leaf 0x2a20261bc1d09b38b)) (.branch 1
  (.leaf 0xe597c2999129038b) (.leaf 0xe111c1596119038b)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x27e755187e239bb8b) (.leaf 0x27dc253e7d867bb8b)) (.branch 1 (.leaf
  0xf7ddf0c254470b8b) (.leaf 0x2ff5df302a4770b8b))) (.branch 2 (.branch 1 (.leaf
  0xa2bd63dc2757b38b) (.leaf 0xbaff42bec567fb8b)) (.branch 1 (.leaf 0x2c682d2604647438b)
  (.leaf 0x2d10fd1a0b677438b))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2494f72853a57f38b) (.leaf 0x267f4415ec423fb8b)) (.branch 1 (.leaf 0x2c699d1804703438b)
  (.leaf 0x2d127d240b733438b))) (.branch 2 (.branch 1 (.leaf 0x2b4d071653b13f38b) (.leaf
  0xb0c263fcd623b38b)) (.branch 1 (.leaf 0xe068c0d95a03038b) (.leaf 0x2e7e8c319aa33038b))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x6fb553c72913bb8b) (.leaf 0x15be5e51e7f32db8b))
  (.branch 1 (.leaf 0x223d75c0fc12638b) (.leaf 0x2041676000c22638b))) (.branch 2 (.branch 1
  (.leaf 0x143fdd5258002d38b) (.leaf 0x12a20c7bc6d32938b)) (.branch 1 (.leaf
  0x28aff6499e112238b) (.leaf 0x2832067591122238b))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x175a2f78792029b8b) (.leaf 0x32a11c45c6c76938b))
  (.branch 1 (.leaf 0x2bbc6779e056238b) (.leaf 0x23e364b91066238b))) (.branch 2 (.branch 1
  (.leaf 0x175b3f46793469b8b) (.leaf 0x34280d5057176d38b)) (.branch 1 (.leaf
  0x29f5245dbf2566b8b) (.leaf 0x961e461b02666b8b)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x15d3be53e8e46db8b) (.leaf 0x30c6bbc2330429380)) (.branch 1 (.leaf 0x1343ea6c4d81b2b80)
  (.leaf 0x323ada504282b2b80))) (.branch 2 (.branch 1 (.leaf 0xd3508c18cf729b80) (.leaf
  0x27e0114a7df73db80)) (.branch 1 (.leaf 0x999e3dbb382a6b80) (.leaf 0x9e7d3e7bc81a6b80)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xa294249c2043d380) (.leaf
  0x26f4d14a72377db80)) (.branch 1 (.leaf 0x9e4e3dbbc42e6b80) (.leaf 0x995d3e7b341e6b80)))
  (.branch 2 (.branch 1 (.leaf 0xb152249cdc47d380) (.leaf 0x2d2338fd8c3469b80)) (.branch 1
  (.leaf 0x16c06953f2b1f2380) (.leaf 0x37c7696ffdb2f2380)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x10d88bfe33c769380) (.leaf 0xd6b4b318f36efb80)) (.branch 1 (.leaf
  0x121ce9a0414374b80) (.leaf 0x3355999c4e4074b80))) (.branch 2 (.branch 1 (.leaf
  0x3090f83230c5ef380) (.leaf 0x6dfd2867135fbb80)) (.branch 1 (.leaf 0x2221e3280fb060380)
  (.leaf 0x203c431400b360380)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2b282185cec6fb380) (.leaf 0x7f522867ef5bbb80)) (.branch 1 (.leaf
  0x20322328007020380) (.leaf 0x2219d3140f7320380))) (.branch 2 (.branch 1 (.leaf
  0x2a13d185c106bb380) (.leaf 0x107ec80e3006af380)) (.branch 1 (.leaf 0x17d95a9ffe7334380)
  (.leaf 0x36a21aa3f17034380)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2d7d7b0d8ff5afb80)
  (.leaf 0x2c535b1583844fb80)) (.branch 1 (.leaf 0x334d69844df1d4b80) (.leaf
  0x324679b842f2d4b80))) (.branch 2 (.branch 1 (.leaf 0x11a9e8163c774f380) (.leaf
  0x7dd22a27d875bb80)) (.branch 1 (.leaf 0x8e130c0302c0380) (.leaf 0x21acd3300c01c0380)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2a2cd1a1c2745b380) (.leaf
  0x6f942a272471bb80)) (.branch 1 (.leaf 0x1c5130c0cc280380) (.leaf 0x20a5d33003c180380)))
  (.branch 2 (.branch 1 (.leaf 0x2b1011a1cdb41b380) (.leaf 0x11afd82a3cb40f380)) (.branch 1
  (.leaf 0x16c0dabbf2c194380) (.leaf 0x17c9fa87fdc294380)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2c4d6b2983470fb80) (.leaf 0x2d6ce8d98f4689b80)) (.branch 1 (.leaf
  0x36a8e977f1c312380) (.leaf 0x37e1b94bfec012380))) (.branch 2 (.branch 1 (.leaf
  0x108f6bda30b589380) (.leaf 0xa1dd251c1b59d380)) (.branch 1 (.leaf 0x2225d0c00fc006380)
  (.branch 1 (.leaf 0x4220fc00c306380) (.leaf 0x27ee21527e469db80)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xb1d2251ce75dd380) (.leaf 0x200690c0000046380)) (.branch 1 (.leaf 0x20de0fc0f0346380)
  (.leaf 0x26ebd1527186ddb80))) (.branch 2 (.branch 1 (.leaf 0x10895be63076c9380) (.leaf
  0x13655a484ef352b80)) (.branch 1 (.leaf 0x122e3a7441f052b80) (.leaf 0x2d72d8e58f85c9b80))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x4de928bd746c2b84) (.leaf 0x1282d8524582c9384))
  (.branch 1 (.leaf 0x327ec8504555c9384) (.leaf 0xb9ae1b66761c2384))) (.branch 2 (.branch 1
  (.leaf 0x220c10a00f0246384) (.leaf 0x303b59462d364d384)) (.branch 1 (.leaf
  0x304be9442de14d384) (.leaf 0x29f4d39dbf2546b84))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x203ef0a000c206384) (.leaf 0x2f46094622f60d384)) (.branch 1 (.leaf
  0x2f32894422210d384) (.leaf 0x296dd39db0e506b84))) (.branch 2 (.branch 1 (.leaf
  0x63361b4687682384) (.leaf 0x177ffb6dfab289b84)) (.branch 1 (.leaf 0x1777eb6ffa6589b84)
  (.leaf 0x2b624289d85182b84)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x37c99adbfdc394384)
  (.leaf 0x2588933ddff79f384)) (.branch 1 (.leaf 0x257ab33fdf209f384) (.leaf
  0x134c49e64de494b84))) (.branch 2 (.branch 1 (.leaf 0xe021bcf957710384) (.leaf
  0x2121c11607b31bb84)) (.branch 1 (.leaf 0x2116f11407641bb84) (.leaf 0xf7f78f2255010b84))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xe801bcf9ab750384) (.leaf
  0x2139b11608735bb84)) (.branch 1 (.leaf 0x213e411408a45bb84) (.leaf 0xffd78f22a9050b84)))
  (.branch 2 (.branch 1 (.leaf 0x124619e442f3d4b84) (.leaf 0x59a400260c7dfb84)) (.branch 1
  (.leaf 0x258c60006010dfb84) (.leaf 0x16c2fad9f2d4d4384)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x16a27afff17134384) (.leaf 0x248c9319d3453f384)) (.branch 1 (.leaf
  0x48eb31bd3923f384) (.leaf 0x321ec9c2415634b84))) (.branch 2 (.branch 1 (.leaf
  0x2e69dbeb99c5b0384) (.leaf 0x18b31320b01bbb84)) (.branch 1 (.leaf 0x21a601300bd6bbb84)
  (.leaf 0x2fecd8d629e2b0b84))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2e0f8beb9605f0384) (.leaf 0xc5b13204c1fbb84)) (.branch 1 (.leaf 0x20b241300416fbb84)
  (.leaf 0x2f9288d62622f0b84))) (.branch 2 (.branch 1 (.leaf 0x1355f9c04e4174b84) (.leaf
  0x268640266c757fb84)) (.branch 1 (.leaf 0x268860246ca27fb84) (.leaf 0x17d87afdfe6674384))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2baab1906b0462384) (.leaf 0x3768eb49f9c069b84))
  (.branch 1 (.leaf 0x1758cb4bf91769b84) (.leaf 0x52692addb2362b84))) (.branch 2 (.branch 1
  (.leaf 0x299523bbb340e6b84) (.leaf 0xda25a5d9174edb84)) (.branch 1 (.leaf
  0xda6da5f91a3edb84) (.leaf 0x98e0860367e6384))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x29ea23bbbc80a6b84) (.leaf 0xedf6a5d9eb4adb84))
  (.branch 1 (.leaf 0xed7da5f9e63adb84) (.leaf 0x1bde0860ca7a6384))) (.branch 2 (.branch 1
  (.leaf 0xb5212afd43422b84) (.leaf 0x12a5f87646f029384)) (.branch 1 (.leaf
  0x1291d874462729384) (.leaf 0x5db6192641322384)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2960143db02766b8f) (.leaf 0x29a5a647b454fd38f)) (.branch 1 (.leaf 0x9a76645b483fd38f)
  (.leaf 0x2000270000006638f))) (.branch 2 (.branch 1 (.leaf 0x2cb86eb407b0f238f) (.leaf
  0x10cb3ff1b3336938f)) (.branch 1 (.leaf 0x10dbbff3b3e46938f) (.leaf 0x31343d89b797f2b8f)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2cb6ee8a07a4b238f) (.leaf
  0x30c98fcfb3272938f)) (.branch 1 (.leaf 0x30dd0fcdb3f02938f) (.leaf 0x11328db7b783b2b8f)))
  (.branch 2 (.branch 1 (.leaf 0x3fb73c00c32638f) (.leaf 0x20c1454604b0bdb8f)) (.branch 1
  (.leaf 0x20b4b5440467bdb8f) (.leaf 0x96bd401b0e426b8f)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x21afe4ce0c15a038f) (.leaf 0x9c9a58bb8963b38f)) (.branch 1 (.leaf
  0x29c36589b8413b38f) (.leaf 0x9e027f3bc32a0b8f))) (.branch 2 (.branch 1 (.leaf
  0xd121d780b723438f) (.leaf 0x2d66cf020f01afb8f)) (.branch 1 (.leaf 0xd7a7f000fd6afb8f)
  (.leaf 0x118e3e45bb5534b8f)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xd109d460b667438f) (.leaf 0x2d684f3c0f15efb8f)) (.branch 1 (.leaf
  0xd78ff3e0fc2efb8f) (.leaf 0x318c8e7bbb4174b8f))) (.branch 2 (.branch 1 (.leaf
  0x29ed17cfbcf1e0b8f) (.leaf 0x137b68a08727bb8f)) (.branch 1 (.leaf 0x13c468808a57bb8f)
  (.leaf 0x1c824f20cd6e038f)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x203924ea00a70038f)
  (.leaf 0x99f55afb4249b38f)) (.branch 1 (.leaf 0x9ad95adb4f39b38f) (.leaf
  0x96827d7b08000b8f))) (.branch 2 (.branch 1 (.leaf 0xcb9fd5c07c09438f) (.leaf
  0xc57ef2603b30fb8f)) (.branch 1 (.leaf 0xc505f2403640fb8f) (.leaf 0x113bbe61b7e794b8f)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xcbb7d6207d4d438f) (.leaf
  0xc566f1803a74fb8f)) (.branch 1 (.leaf 0xc51df1a03704fb8f) (.leaf 0x313d0e5fb7f3d4b8f)))
  (.branch 2 (.branch 1 (.leaf 0x963e7ebb04340b8f) (.leaf 0x20c3b6ae04c0dbb8f)) (.branch 1
  (.leaf 0xb046ac0417dbb8f) (.leaf 0x202d44d600644038f)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x21b527260c65c638f) (.leaf 0x2130455c08165db8f)) (.branch 1 (.leaf
  0x143b55e08c15db8f) (.leaf 0x9e5141bbc42c6b8f))) (.branch 2 (.branch 1 (.leaf
  0x119d0dafbbf252b8f) (.leaf 0xd716cea0f71c9b8f)) (.branch 1 (.leaf 0xd75dce80fa6c9b8f)
  (.branch 1 (.leaf 0x2d1b3e920bd55238f) (.leaf 0x319bbd91bbe612b8f))))))))) (.branch 65
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0xd6fecd40f6589b8f) (.leaf 0xd775cd60fb289b8f)) (.branch 1 (.leaf 0x2d19beac0bc11238f)
  (.leaf 0x9e82427bc8186b8f))) (.branch 2 (.branch 1 (.leaf 0x29cd965db8f21d38f) (.leaf
  0x29bf565fb8251d38f)) (.branch 1 (.leaf 0x21bce71a0ca68638f) (.leaf 0x227657f094b488230))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x37eaeedb7f2363a30) (.leaf 0xc76bd0d050263a30))
  (.branch 1 (.leaf 0x2b7747195e6588a30) (.leaf 0xe6a4ead19d54da30))) (.branch 2 (.branch 1
  (.leaf 0xa2f04b942b2a6a30) (.leaf 0x9c7276f3893a6a30)) (.branch 1 (.leaf
  0x13c68e44d3044d230) (.leaf 0x742a5c2f6257da30))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x103defd6ad4296a30) (.leaf 0x142fbc00d76396a30)) (.branch 1 (.leaf
  0x29ee652b3cf47d230) (.leaf 0x13181fa0cbb4b8a30))) (.branch 2 (.branch 1 (.leaf
  0x8c2668b202353230) (.leaf 0x2b68955d5a0253230)) (.branch 1 (.leaf 0x2c1f8f490165b8230)
  (.leaf 0x31c44f86bd943ea30)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x6150592e6f3d5a30)
  (.leaf 0x22b726449cd2d5a30)) (.branch 1 (.leaf 0x172cff6f77453e230) (.leaf
  0x201765e48005fba30))) (.branch 2 (.branch 1 (.leaf 0x36144ccf6b9210230) (.leaf
  0x2da74f1911b310230)) (.branch 1 (.leaf 0xad7450d4ad4fb230) (.leaf 0x167e1e8b6ff5cba30))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x20b667a0846220230) (.leaf
  0x27eb0476fe4320230)) (.branch 1 (.leaf 0xf79fe62a524cb230) (.leaf 0x25bca7d6e2940e230)))
  (.branch 2 (.branch 1 (.leaf 0x316e1dc2b9f3e5230) (.leaf 0x125b1e14c3d2e5230)) (.branch 1
  (.leaf 0x2926673f28450ea30) (.leaf 0x309affa2b1269ea30)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x659f5b6ea4175a30) (.leaf 0x2325660906075a30)) (.branch 1 (.leaf
  0x179e1f4b7bf79e230) (.leaf 0x21c1f5c08cb75ba30))) (.branch 2 (.branch 1 (.leaf
  0x15aa6ceb6720b0230) (.leaf 0x2eb75f3d1d01b0230)) (.branch 1 (.leaf 0xa80a52946665b230)
  (.leaf 0x154dfeaf63476ba30))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x146a78488d080230) (.leaf 0x27030452f2f180230)) (.branch 1 (.leaf 0xfe44e46a9966b230)
  (.leaf 0x6a7a7f2ee26ae230))) (.branch 2 (.branch 1 (.leaf 0x10fd6de6b54145230) (.leaf
  0x13705e30cf6045230)) (.branch 1 (.leaf 0x90b971b24f7aea30) (.leaf 0x92e64eb28f628a30))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x124fedc0c361c3230) (.leaf 0x115dbe16b940c3230))
  (.branch 1 (.leaf 0x5b32402e22728230) (.leaf 0x2f844db6a597ed230))) (.branch 2 (.branch 1
  (.leaf 0x7f4c7a2fef006230) (.leaf 0x20ca547484d106230)) (.branch 1 (.leaf
  0x366cdd5f6f46eda30) (.branch 1 (.leaf 0xacea6d94a67dd230) (.leaf
  0x2d96eccd110036230)))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x160abf1b6b2136230) (.leaf 0x203e363080b6dda30)) (.branch 1 (.leaf
  0x373e1cbb77f618230) (.leaf 0x22af25909c61f3a30))) (.branch 2 (.branch 1 (.leaf
  0x260b0646e640f3a30) (.leaf 0x11b9dc52bd2718a30)) (.branch 1 (.leaf 0xf93790c26332d235)
  (.leaf 0x2b16f001ce0126a35)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x9a213d7b42026a35)
  (.leaf 0x163389e5ece22da35)) (.branch 1 (.leaf 0x32c53b8280328a35) (.leaf
  0x1691b98a70c123a35))) (.branch 2 (.branch 1 (.leaf 0xd03ba5c0ae023a35) (.leaf
  0xb89b351e2d228235)) (.branch 1 (.leaf 0x12c2f8e9c82718a35) (.leaf 0x282d62db90e513a35)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2ba8610deac413a35) (.leaf
  0xc45080002f618235)) (.branch 1 (.leaf 0x753516276e71da35) (.leaf 0x2ee3386f9ed516235)))
  (.branch 2 (.branch 1 (.leaf 0x15753bb9e4f416235) (.leaf 0x9e1618bbc361d235)) (.branch 1
  (.leaf 0x21c1315c0cb67ba35) (.leaf 0x33e9db6e547470a35)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1056e8b82e5570a35) (.leaf 0xa8151b5c6677b235)) (.branch 1 (.leaf
  0x10ba18d7b2767ea35) (.leaf 0x51cf1da5a4475235))) (.branch 2 (.branch 1 (.leaf
  0x2d1520c206575235) (.leaf 0x374ef83e78a77e235)) (.branch 1 (.leaf 0x2478538652524ea35)
  (.leaf 0x11785a8bba6045235)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1205695dc04145235) (.leaf 0x888636f98834e235)) (.branch 1 (.leaf
  0x34a899325c624b235) (.leaf 0x20bd630004a040235))) (.branch 2 (.branch 1 (.leaf
  0x7eef0d67e8140235) (.leaf 0xe1f79db96b34ba35)) (.branch 1 (.leaf 0x2009b1780004dba35)
  (.leaf 0x1450fb4a58c6d0a35)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xf43f89c22e7d0a35)
  (.leaf 0xada1191cad5db235)) (.branch 1 (.leaf 0x11e0f8f3bec4dea35) (.leaf
  0x4d451fe56f6d5235))) (.branch 2 (.branch 1 (.leaf 0x235a12282cd7d5235) (.leaf
  0x36e0481a7415de235)) (.branch 1 (.leaf 0x2575a3a25ee0eea35) (.leaf 0x11237aafb6d2e5235)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x33367979ccf3e5235) (.leaf
  0x861634b9431ee235)) (.branch 1 (.leaf 0x1393791650d0eb235) (.leaf 0x213153240812e0235)))
  (.branch 2 (.branch 1 (.leaf 0x26f600f27233e0235) (.leaf 0x2e6ec9ff9a01eba35)) (.branch 1
  (.leaf 0xe797a179a718da35) (.leaf 0x6f8531a724386235)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x13560cc086286235) (.leaf 0x138ddafe50a08d235)) (.branch 1 (.leaf
  0x86560a3944188235) (.leaf 0x132aea91cc8383235))) (.branch 2 (.branch 1 (.leaf
  0x311ee947b6a283235) (.leaf 0x572104a5e9088a35)) (.branch 1 (.leaf 0x16e8fbf27465b8235)
  (.branch 1 (.leaf 0x2355d1c02ca7b3235) (.leaf 0x4d202165686b3235))))))))))) (.branch 258
  (.branch 129 (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x11df5b1bbeb4b8a35) (.leaf 0x2ad5a279caa5bd235)) (.branch 1 (.leaf
  0x2f3c6b742297b6a35) (.leaf 0x345068a258b6b6a35))) (.branch 2 (.branch 1 (.leaf
  0x202f32900074bda35) (.leaf 0x24079103bfe117335)) (.branch 1 (.leaf 0x34030aa2558470b35)
  (.leaf 0x147b0a9e5a8770b35)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x280ba200001217b35)
  (.leaf 0x30d3091bb3867eb35)) (.branch 1 (.leaf 0x263ec185e91319b35) (.leaf
  0x260631b9e61019b35))) (.branch 2 (.branch 1 (.leaf 0xd298a180c757e335) (.leaf
  0x494524a53a24eb35)) (.branch 1 (.leaf 0xcdb1ad4093729b35) (.leaf 0xc931ae8063429b35)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2bb22149ec514e335) (.leaf
  0x166bd96def3527b35)) (.branch 1 (.leaf 0xd562cc055040335) (.leaf 0x217592f00a5340335)))
  (.branch 2 (.branch 1 (.leaf 0x1390fa6e50c627335) (.leaf 0x21d5b0900d467bb35)) (.branch 1
  (.leaf 0x343aa80e57d31cb35) (.leaf 0x1453783258d01cb35)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x98c3393b2b57b335) (.leaf 0x30aadbb7b1d112b35)) (.branch 1 (.leaf
  0x535b0165bb475335) (.leaf 0x4a8302a54b775335))) (.branch 2 (.branch 1 (.leaf
  0x2d5228b40e2212335) (.leaf 0x247020e651f522b35)) (.branch 1 (.leaf 0x11949b47bb9045335)
  (.leaf 0x10ed7b7bb49345335)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2bb7d3e5ee0622335) (.leaf 0x14c498fe5d924b335)) (.branch 1 (.leaf
  0x10c106007072c335) (.leaf 0x212dd05c08042c335))) (.branch 2 (.branch 1 (.leaf
  0x3537fbfde2614bb35) (.leaf 0x209b0b60ee39bb35)) (.branch 1 (.leaf 0x33ea18285476fcb35)
  (.leaf 0x349198145b75fcb35)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x97133b5b1109b335)
  (.leaf 0x10b9db91b274f2b35)) (.branch 1 (.leaf 0x4edc030581195335) (.leaf
  0x24d9300c571295335))) (.branch 2 (.branch 1 (.leaf 0x2d4318920d87f2335) (.leaf
  0x247750c05250c2b35)) (.branch 1 (.leaf 0x31441b61b835a5335) (.leaf 0x112bab5db736a5335)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xbb523c3eda3c2335) (.leaf
  0x14d3a8d85e37ab335)) (.branch 1 (.leaf 0x20bde04604a2cc335) (.leaf 0x21a0d07a0ba1cc335)))
  (.branch 2 (.branch 1 (.leaf 0x1528fbdbe1c4abb35) (.leaf 0x21bf721a0cb4f7b35)) (.branch 1
  (.leaf 0x15a319bbe6d190335) (.leaf 0x15eb7987e9d290335)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x9937119b347f7335) (.leaf 0x2c121a0200d39e335)) (.branch 1 (.leaf
  0x51b729c5a46f9335) (.leaf 0x24b372a05545f9335))) (.branch 2 (.branch 1 (.leaf
  0x31e99901bf209eb35) (.leaf 0x259ca153e0f7ae335)) (.branch 1 (.leaf 0x117899cdba62c9335)
  (.leaf 0x3100f9f1b561c9335))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2b7ad2505f04aeb35) (.leaf 0x34a85a745c60c7335)) (.branch 1 (.leaf
  0x3bad1d5b605a0b35) (.leaf 0x3dad1e9b906a0b35))) (.branch 2 (.branch 1 (.leaf
  0x15547977e393c7b35) (.leaf 0x292577a9874c2330)) (.branch 1 (.leaf 0x36b06cdb7211a5b30)
  (.leaf 0x37b97ce77d12a5b30)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x919f4792787c2b30)
  (.leaf 0x2df3ccad14e78bb30)) (.branch 1 (.leaf 0x2b1ac4334e72ecb30) (.leaf
  0xa1a740f4171ecb30))) (.branch 2 (.branch 1 (.leaf 0x10080faeab148b330) (.leaf
  0x7a8a7c2fb17bbb30)) (.branch 1 (.leaf 0xf22ef5ca182dcb30) (.leaf 0x305bff60ae81dcb30)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0xa5ed4c144e4bb330) (.leaf
  0x12b1df2ac774f2b30)) (.branch 1 (.leaf 0x94f148b2d1195330) (.leaf 0x8df94b7221295330)))
  (.branch 2 (.branch 1 (.leaf 0x374a8c297887f2330) (.leaf 0x11a7ce4abc643eb30)) (.branch 1
  (.leaf 0x261306d4e6f159b30) (.leaf 0x2651f6e8e9f259b30)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xc547d4903973e330) (.leaf 0x1726a2800777b30)) (.branch 1 (.leaf 0x15f7cd036a6210330)
  (.leaf 0x357fcd3f656110330))) (.branch 2 (.branch 1 (.leaf 0x29fdf5a13ff477330) (.leaf
  0x367dddcd6ff747b30)) (.branch 1 (.leaf 0xde666c859220330) (.leaf 0x217c96508a9120330))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x337efeced00447330) (.leaf
  0x25d0a61ae3640e330)) (.branch 1 (.leaf 0x116dde84b9f169330) (.leaf 0x1125deb8b6f269330)))
  (.branch 2 (.branch 1 (.leaf 0xb6ed5195c970eb30) (.leaf 0x1080ee52b015deb30)) (.branch 1
  (.leaf 0x65b86ccea80b9b30) (.leaf 0x25fe76f0e583b9b30)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0xd7c5d510fe6de330) (.leaf 0x1b876ba8c7697b30)) (.branch 1 (.leaf
  0x15913d1b6613f0330) (.leaf 0x15d96d276910f0330))) (.branch 2 (.branch 1 (.leaf
  0x299875b9338597330) (.leaf 0x35536dd56386a7b30)) (.branch 1 (.leaf 0x168a67489e3c0330)
  (.leaf 0x108a64886e0c0330))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x34a94ed6dc75a7330) (.leaf 0x6b8a602ef15ee330)) (.branch 1 (.leaf 0x1103be9cb58089330)
  (.leaf 0x317beea0ba8389330))) (.branch 2 (.branch 1 (.leaf 0x2b3ed50150e6eeb30) (.leaf
  0x290a945d24f522b30)) (.branch 1 (.leaf 0x135d1ffcce9045330) (.leaf 0x32245fc0c19345330))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x229b075e9b0622330) (.leaf 0x2fc7cf8aa8666b330))
  (.branch 1 (.leaf 0x7038714f2f30c330) (.leaf 0x7e1f728fdf00c330))) (.branch 2 (.branch 1
  (.leaf 0xe343c8917956bb30) (.leaf 0x2a94a4e547965b330)) (.branch 1 (.leaf
  0xeb79c7b1d033c330) (.branch 1 (.leaf 0xdaedc4712003c330) (.leaf
  0x276ed7e6f8655bb30))))))))) (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4
  (.branch 2 (.branch 1 (.leaf 0x379ddc0d7bf512330) (.leaf 0x224657ac919075b30)) (.branch 1
  (.leaf 0x2c2e7909e9375b30) (.leaf 0x125ebf0ec40612b30))) (.branch 2 (.branch 1 (.leaf
  0xfeddc3229f55ca8f) (.leaf 0x9d5a447b9663b28f)) (.branch 1 (.leaf 0xafc17afcc933b28f) (.leaf
  0x36350ce5ecf05c28f)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2cfb0cb40a823428f) (.leaf
  0x34947fe2ae15328f)) (.branch 1 (.leaf 0x257a04165f145328f) (.leaf 0x13730c63cf8734a8f)))
  (.branch 2 (.branch 1 (.leaf 0x2cfc9c8a0a967428f) (.leaf 0x93d77c02af51328f)) (.branch 1
  (.leaf 0x2b7df4285f001328f) (.leaf 0x33740c5dcf9374a8f))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2e58df3399111c28f) (.leaf 0x215bb74609827ba8f)) (.branch 1 (.leaf
  0x7c614ae7c777ba8f) (.leaf 0x14a0ffe45c141ca8f))) (.branch 2 (.branch 1 (.leaf
  0xe55fd8798f7d028f) (.leaf 0x9c956cdb894b728f)) (.branch 1 (.leaf 0x2b0dd525cd61b728f)
  (.leaf 0x14cd0d505df2d0a8f)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0xd11de3e0b70b828f)
  (.leaf 0x22a7464b9be3dfa8f)) (.branch 1 (.leaf 0x6a505a3ee16dfa8f) (.leaf
  0x33599ee9ce75b8a8f))) (.branch 2 (.branch 1 (.leaf 0xd105e000b64f828f) (.leaf
  0x89b76759bf79fa8f)) (.branch 1 (.leaf 0x2bb8f59dee029fa8f) (.leaf 0x13578ed7ce61f8a8f))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2fc12e86281390a8f) (.leaf
  0x136f5cc0870f7a8f)) (.branch 1 (.leaf 0x7dd56247d85f7a8f) (.leaf 0x36392e51ed169028f)))
  (.branch 2 (.branch 1 (.leaf 0x205cb51a01944028f) (.leaf 0xf2e2e5021f72728f)) (.branch 1
  (.leaf 0x33dfadb854022728f) (.leaf 0x2a5bb5cdc49140a8f)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x84206a392132828f) (.leaf 0xc3b0ed602804fa8f)) (.branch 1 (.leaf
  0x37318d3e77754fa8f) (.leaf 0x24d82674571628a8f))) (.branch 2 (.branch 1 (.leaf
  0x224e369d92076828f) (.leaf 0xc3c9ee802940fa8f)) (.branch 1 (.leaf 0x372fbd0077610fa8f)
  (.leaf 0x2b5c764a570268a8f))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x297da61bb17000a8f) (.leaf 0x2d98fd51911367a8f)) (.branch 1 (.leaf 0x3573beb9e4e667a8f)
  (.leaf 0x272336cc74750028f))) (.branch 2 (.branch 1 (.leaf 0x202b67900066cc28f) (.leaf
  0x2d961fe590f5aba8f)) (.branch 1 (.leaf 0x15777c0de500aba8f) (.leaf 0x2a6af747c563cca8f))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x28f187162311a4a8f) (.leaf 0xc521c5c0372c3a8f))
  (.branch 1 (.leaf 0x171b1fb47687c3a8f) (.leaf 0x260327c1e614a428f))) (.branch 2 (.branch 1
  (.leaf 0x22fdb7282305e4a8f) (.leaf 0xc509c62036683a8f)) (.branch 1 (.leaf
  0x171c3f8a769383a8f) (.leaf 0xb9777ffe600e428f))))))) (.branch 32 (.branch 16 (.branch 8
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x9676491b0828ca8f) (.leaf 0xf011ce42011eb28f))
  (.branch 1 (.leaf 0x140bbf0c55e4eb28f) (.leaf 0x73cf44675878c28f))) (.branch 2 (.branch 1
  (.leaf 0x252e9201db8688a84) (.leaf 0x33086a744b15ef284)) (.branch 1 (.leaf
  0x11e4799c3ee0ef284) (.leaf 0x28ba52d61e8388284)))) (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x205db286019560284) (.leaf 0xf2e49cc21f607284)) (.branch 1 (.leaf 0x33dfca24540307284)
  (.leaf 0x2a5cb251c49060a84))) (.branch 2 (.branch 1 (.leaf 0x21f5a2860e5520284) (.leaf
  0x105369cc2e3647284)) (.branch 1 (.leaf 0x34991a245bc347284) (.leaf 0x2adf3251cb5020a84)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x25e7613e64b6c8284) (.leaf
  0x16e2094bf425afa84)) (.branch 1 (.leaf 0xc2a8aa381d0afa84) (.leaf 0x8db31e9a1b3c8a84)))
  (.branch 2 (.branch 1 (.leaf 0x64623926921e4284) (.leaf 0x12dce8d8494283284)) (.branch 1
  (.leaf 0x11b07b303cb783284) (.leaf 0x29405345ac24e4a84)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x20a3602a03c20c284) (.leaf 0x2dce985f93516ba84)) (.branch 1 (.leaf
  0x159efbb7e6a46ba84) (.leaf 0x2a88f0fdc6c70ca84))) (.branch 2 (.branch 1 (.leaf
  0x21ac602a0c024c284) (.leaf 0x2eac685f9c912ba84)) (.branch 1 (.leaf 0x15e0fbb7e9642ba84)
  (.leaf 0x2ab3f0fdc9074ca84)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x24c490add611a4a84) (.leaf 0x1719fbe7f672c3a84)) (.branch 1 (.leaf
  0x2c53f80f8387c3a84) (.leaf 0x284eb07a1314a4284))) (.branch 2 (.branch 1 (.leaf
  0x37f4fb31ff9674284) (.leaf 0x586907bdff513284)) (.branch 1 (.leaf 0x33b1393aa0013284)
  (.leaf 0x317c5be63a9374a84)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2e01d88995759c284)
  (.leaf 0x20ea40fc05e6fba84)) (.branch 1 (.leaf 0x6cc43147013fba84) (.leaf
  0x1389585e50709ca84))) (.branch 2 (.branch 1 (.leaf 0x2e7fd8899ab5dc284) (.leaf
  0x217140fc0a26bba84)) (.branch 1 (.leaf 0x80513147fd3bba84) (.leaf 0x14f7985e5fb0dca84)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x320e080e40a634a84) (.leaf
  0x2599434460c553a84)) (.branch 1 (.leaf 0x28040ac153053a84) (.leaf 0xc8608d985a334284)))
  (.branch 2 (.branch 1 (.leaf 0x17c9599dfdc118284) (.leaf 0x269561e86d527fa84)) (.branch 1
  (.leaf 0x2295e20018a77fa84) (.leaf 0x1150d94a38c418a84)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x2fba991a27d2f0a84) (.leaf 0x120325007b197a84)) (.branch 1 (.leaf
  0x6f9b1b8724497a84) (.leaf 0x354259cde2d7f0284))) (.branch 2 (.branch 1 (.leaf
  0x2fc1491a2812b0a84) (.leaf 0x138f2500871d7a84)) (.branch 1 (.leaf 0x7dc51b87d84d7a84)
  (.branch 1 (.leaf 0x363949cded17b0284) (.leaf 0x3245daa242f158a84)))))))))) (.branch 129
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x247ab2d7d2623f284) (.leaf 0x322b13fa7973f284)) (.branch 1 (.leaf 0xcbdfa7587f458284)
  (.leaf 0x58a6027dff413280))) (.branch 2 (.branch 1 (.leaf 0x11046b86359174a80) (.leaf
  0x3377c8504fb074a80)) (.branch 1 (.leaf 0x87320ce152513a80) (.leaf 0x20e7b0a005e7fba80))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x14f1a83e5f729ca80) (.leaf 0x2f7edbe825539ca80))
  (.branch 1 (.leaf 0xb2f6049cf36fb280) (.leaf 0x2171b0a00a27bba80))) (.branch 2 (.branch 1
  (.leaf 0x138f683e50b2dca80) (.leaf 0x2ffcdbe82a93dca80)) (.branch 1 (.leaf
  0xa10d049c0f6bb280) (.leaf 0x2597b31860c453a80))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x2cfe08b98aa134280) (.leaf 0x168b0b6ff08034280)) (.branch 1 (.leaf
  0x2930b3f1aa1553280) (.leaf 0x6b561926ef69fa80))) (.branch 2 (.branch 1 (.leaf
  0x30e7e90c3463f8a80) (.leaf 0x33555ada4e42f8a80)) (.branch 1 (.leaf 0x901d17ba4279f280)
  (.leaf 0xaf322a041577a80)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x165a298bee7010280)
  (.leaf 0xde72a5d945110280)) (.branch 1 (.leaf 0x2b29a2c3cec477280) (.leaf
  0x1a4f22a0bd537a80))) (.branch 2 (.branch 1 (.leaf 0x1527698be1b050280) (.leaf
  0xe94aa5d9b9150280)) (.branch 1 (.leaf 0x2a15d2c3c10437280) (.leaf 0x46ab2add1c6df280))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2d0eca338b53b8280) (.leaf
  0x36a1d9e5f172b8280)) (.branch 1 (.leaf 0x88eb2441b17dfa80) (.leaf 0x1734590ff7950fa80)))
  (.branch 2 (.branch 1 (.leaf 0x35e6191ad0068a80) (.leaf 0x24de6247d72168a80)) (.branch 1
  (.leaf 0x31bd49e63d440f280) (.leaf 0x2ec15ab79d76e7a80)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x7594116771380280) (.leaf 0x21d192c00d3280280)) (.branch 1 (.leaf
  0x34362a5e57a7e7280) (.leaf 0x2dc02ab792b6a7a80))) (.branch 2 (.branch 1 (.leaf
  0x77db11678d3c0280) (.leaf 0x208a42c002f2c0280)) (.branch 1 (.leaf 0x3448aa5e5867a7280)
  (.leaf 0x12ce0a3048a54f280))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x24f32ae123028280) (.leaf 0x262c1178681128280)) (.branch 1 (.leaf 0x2c398ad982744fa80)
  (.leaf 0x3717db85f66783a80))) (.branch 2 (.branch 1 (.leaf 0x2ad60241c02e4280) (.leaf
  0x60a23f26623e4280)) (.branch 1 (.leaf 0x11b01b6c3cb683280) (.leaf 0x10295b022c746b280))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x756039c76e10c280) (.leaf 0x1c3504a0cc00c280))
  (.branch 1 (.leaf 0x159e9bebe6a56ba80) (.leaf 0xf57ab0223b42b280))) (.branch 2 (.branch 1
  (.leaf 0x780f39c79214c280) (.leaf 0x8d504a03004c280)) (.branch 1 (.leaf 0x15e09bebe9652ba80)
  (.leaf 0x12dec8ba4957c3280))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x22feb31ba332a4a80) (.leaf 0x250090cdd913a4a80)) (.branch 1 (.leaf
  0x2c5398538386c3a80) (.leaf 0xf36ce2a2253c728b))) (.branch 2 (.branch 1 (.leaf
  0xaa4458bc836a0a8b) (.leaf 0x2981965db217a0a8b)) (.branch 1 (.leaf 0x35ca8ec3e882c7a8b)
  (.leaf 0x2c1a0eac0124afa8b)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x534d6325bb1c8a8b)
  (.leaf 0x22e605e42190c8a8b)) (.branch 1 (.leaf 0x131d8e45cbf5af28b) (.leaf
  0x2c1bae920130efa8b))) (.branch 2 (.branch 1 (.leaf 0xb6c860c5ba588a8b) (.leaf
  0x28da35da218488a8b)) (.branch 1 (.leaf 0x331b8e7bcbe1ef28b) (.leaf 0x2dc04d2b92b787a8b)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x77d468a78d2e028b) (.leaf
  0x2088455c02f3e028b)) (.branch 1 (.leaf 0x3448cdc258668728b) (.leaf 0x2d967fb990f4aba8b)))
  (.branch 2 (.branch 1 (.leaf 0xad0f727ca61cca8b) (.leaf 0x96554f1b040cca8b)) (.branch 1
  (.leaf 0x14718f505a25ab28b) (.leaf 0xc527c000373c3a8b)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x263f27a1e916a428b) (.leaf 0x226184779337a428b)) (.branch 1 (.leaf
  0x32e62ce9c9a2c328b) (.leaf 0xc50fc3e036783a8b))) (.branch 2 (.branch 1 (.leaf
  0xba3779fe902e428b) (.leaf 0x855b4499323e428b)) (.branch 1 (.leaf 0x12e70cd7c9b68328b)
  (.leaf 0xf017cb82010eb28b)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x27a0f4267a858c28b) (.leaf 0x2037f7f000a48c28b)) (.branch 1 (.leaf
  0x16014c51eac1eba8b) (.leaf 0x20f4471a06433ba8b))) (.branch 2 (.branch 1 (.leaf
  0x34b2cf845cd65ca8b) (.leaf 0xfa5dc5226f75ca8b)) (.branch 1 (.leaf 0xafde7f3cc923b28b)
  (.leaf 0x877b4a395c453a8b)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x37f60f027fa13428b)
  (.leaf 0xc830cd405803428b)) (.branch 1 (.leaf 0x2576f44a5f155328b) (.leaf
  0x2283849d95d013a8b))) (.branch 2 (.branch 1 (.leaf 0x37f73f3c7fb57428b) (.leaf
  0xc84acea05947428b)) (.branch 1 (.leaf 0x2b7b04745f011328b) (.leaf 0x9b7641bb6a77b28b)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x16233c85ec321c28b) (.leaf
  0x2e10df5396131c28b)) (.branch 1 (.leaf 0x7c4e4f27c767ba8b) (.leaf 0xb135b6041457a8b)))
  (.branch 2 (.branch 1 (.leaf 0x165a4e17ee713028b) (.leaf 0xde74dc194503028b)) (.branch 1
  (.leaf 0x2b27555fcec55728b) (.leaf 0x913453027633f28b)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x17cdadae7df65828b) (.leaf 0xcbade7807d75828b)) (.branch 1 (.leaf
  0x269d05d9edb23fa8b) (.leaf 0x31f750e27777f28b))) (.branch 2 (.branch 1 (.leaf
  0x17cbbd907de21828b) (.leaf 0xcb95e4607c31828b)) (.branch 1 (.leaf 0xbb4f5e7eda67fa8b)
  (.branch 1 (.leaf 0x9ac66b7b4f01728b) (.leaf 0x34dc3d165e9570a8b))))))))) (.branch 65
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2f6fcec024b470a8b) (.leaf 0x7e8565e7e2117a8b)) (.branch 1 (.leaf 0x37a32e337c3629b34)
  (.leaf 0x6898646eca54e334))) (.branch 2 (.branch 1 (.leaf 0x682e644ec724e334) (.leaf
  0x13202d0ecc1129334)) (.branch 1 (.leaf 0x6d2c5e4f0a560334) (.leaf 0x3390ceaed0c607334))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x1380deacd01107334) (.leaf 0x2a0ac6d9408260b34))
  (.branch 1 (.leaf 0x2eee8e8b1f5550334) (.leaf 0x240165c13f3637334))) (.branch 2 (.branch 1
  (.leaf 0x240855c33fe137334) (.leaf 0x10718db6af7250b34)) (.branch 1 (.leaf
  0x23012663233619334) (.leaf 0x30d60e16b3a57eb34))))) (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x30d18e14b3727eb34) (.leaf 0x2850e55e931119b34)) (.branch 1 (.leaf
  0x335d7fa0ce9145334) (.leaf 0x6b474eaeef222334))) (.branch 2 (.branch 1 (.leaf
  0x6aa54e8ee2522334) (.leaf 0x17dfcc9d7eb645b34)) (.branch 1 (.leaf 0x27067748f2f20c334)
  (.leaf 0x1537cf3d62616bb34)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x153fcf3f62b66bb34)
  (.leaf 0x2a34747542d50cb34)) (.branch 1 (.leaf 0x2eb7fc271d023c334) (.leaf
  0x1dab4528d915bb34))) (.branch 2 (.branch 1 (.leaf 0x21d584508d465bb34) (.leaf
  0x303a7f1aad253cb34)) (.branch 1 (.leaf 0x243a7f0919175b34) (.leaf 0x30adfcbab1f212b34))))))
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x309a5cb8b12512b34) (.leaf
  0x8db94cd21b675334)) (.branch 1 (.leaf 0x133bff86cd34a5334) (.leaf 0x269484cced57c2334)))
  (.branch 2 (.branch 1 (.leaf 0x696a4ceed80c2334) (.leaf 0x17b91cbb7d13a5b34)) (.branch 1
  (.leaf 0x6e3076ef157ec334) (.leaf 0x3528cf1b61c48bb34)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x1518ff1961138bb34) (.leaf 0x2a1784534170ecb34)) (.branch 1 (.leaf
  0x2ede4c011ea7dc334) (.leaf 0x1eeb4748e34bbb34))) (.branch 2 (.branch 1 (.leaf
  0x20984768ee3bbb34) (.leaf 0x105b9f3cae80dcb34)) (.branch 1 (.leaf 0x250a7d6923495b34)
  (.leaf 0x30b6cc9cb257f2b34))))) (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x10bb5c9eb280f2b34) (.leaf 0x28e264eb221395334)) (.branch 1 (.leaf 0x1370fd2acf63c9334)
  (.leaf 0x587755f5ff0aeb34))) (.branch 2 (.branch 1 (.leaf 0x57e155d5f27aeb34) (.leaf
  0x37ed9e177f44c9b34)) (.branch 1 (.leaf 0x241956fd43f080b34) (.leaf 0x35544db76393e7b34))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x154d5db56344e7b34) (.leaf 0xbcd35c0f3d780334))
  (.branch 1 (.leaf 0x101ffd92ac00b0b34) (.leaf 0x21b2b6d88c63d7b34))) (.branch 2 (.branch 1
  (.leaf 0x21bf46da8cb4d7b34) (.leaf 0x2ea29eaf1c27b0334)) (.branch 1 (.leaf
  0x22f257a9063f9b34) (.branch 1 (.leaf 0x2c152d0f00f09e334) (.leaf
  0x2c01ad0d00279e334)))))))) (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2
  (.branch 1 (.leaf 0x8c2d6472044f9334) (.leaf 0x13ea78745477fcb31)) (.branch 1 (.leaf
  0xa5f7001c4e49b331) (.leaf 0xa561003c4339b331))) (.branch 2 (.branch 1 (.leaf
  0x35660b49e450fc331) (.leaf 0x24ec306c581095331)) (.branch 1 (.leaf 0x17496b267873f2331)
  (.leaf 0x174e5b2478a4f2331)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x2ba13351e83795b31)
  (.leaf 0x11447b3db834a5331)) (.branch 1 (.leaf 0x88350779857c2331) (.leaf
  0x288990759880c2331))) (.branch 2 (.branch 1 (.leaf 0x2cc008000813a5b31) (.leaf
  0xbc101a04a3cc331)) (.branch 1 (.leaf 0xde3686f9430abb31) (.leaf 0xdf3f86d94e7abb31)))))
  (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0x29a7d327b484ccb31) (.leaf
  0x26cf3144706700331)) (.branch 1 (.leaf 0x137eca0e500467331) (.leaf 0x3392da0c50d367331)))
  (.branch 2 (.branch 1 (.leaf 0xa073279c04000b31) (.leaf 0x1335da63ccf069331)) (.branch 1
  (.leaf 0x253f72165c630eb31) (.leaf 0x254a12145cb40eb31)))) (.branch 4 (.branch 2 (.branch 1
  (.leaf 0x37b2d95e7cd769b31) (.leaf 0x358e1322cd459331)) (.branch 1 (.leaf
  0x11a4c947bc473eb31) (.leaf 0x31ac7945bc903eb31))) (.branch 2 (.branch 1 (.leaf
  0x8ad220f9cf359b31) (.leaf 0xf0f792a20b330b31)) (.branch 1 (.leaf 0x2044f26000d057b31)
  (.leaf 0x91262000757b31)))))) (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf
  0x2d8c7a17909430331) (.leaf 0x27bdb15c7c16e0331)) (.branch 1 (.leaf 0x14a97a165c7587331)
  (.leaf 0x14ae6a145ca287331))) (.branch 2 (.branch 1 (.leaf 0xaf53261cc31e0b31) (.leaf
  0x320bba7bc08189331)) (.branch 1 (.leaf 0x244b720e5012eeb31) (.leaf 0x45a120c50c5eeb31))))
  (.branch 4 (.branch 2 (.branch 1 (.leaf 0x168ee94670a689b31) (.leaf 0x22d4212a20a5b9331))
  (.branch 1 (.leaf 0x1083d95fb036deb31) (.leaf 0x1094695db0e1deb31))) (.branch 2 (.branch 1
  (.leaf 0x2828d2179082b9b31) (.leaf 0x3031b9322cc2d0b31)) (.branch 1 (.leaf
  0x1bbb2780ca1b7b31) (.leaf 0x1b8427a0c76b7b31))))) (.branch 8 (.branch 4 (.branch 2 (.branch
  1 (.leaf 0xeb4ea0f9ce5d0331) (.leaf 0x35d53b53e8f61c331)) (.branch 1 (.leaf
  0x276f732678657bb31) (.leaf 0x277a132478b27bb31))) (.branch 2 (.branch 1 (.leaf
  0x3453186e58d11cb31) (.leaf 0xb91634be49175b31)) (.branch 1 (.leaf 0x12755801c4f212b31)
  (.leaf 0x12625803c42512b31)))) (.branch 4 (.branch 2 (.branch 1 (.leaf 0x24a9c07654b675331)
  (.leaf 0x2c6f381a04b545b31)) (.branch 1 (.leaf 0x319935024d622b31) (.leaf
  0x230b5352240122b31))) (.branch 2 (.branch 1 (.leaf 0x30ed1b27b49245331) (.leaf
  0x9c0e33db8222cb31)) (.branch 1 (.leaf 0xfcf5b4828b14b331) (.branch 1 (.leaf
  0xfc7fb4a28664b331) (.leaf 0x12c200008052c331))))))))))))))

set_option maxHeartbeats 8000000 in
-- Check the exact stored size at every branch.
private theorem generatedTenth_root_two_row_descriptor_index_tree_valid :
    generatedTenthRootTwoRowDescriptorIndexTree.Valid := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Compare every original array entry in the complete ordered list.
set_option backward.isDefEq.respectTransparency false in
private theorem generatedTenth_root_two_row_descriptor_index_tree_list :
    generatedTenthRootTwoRowDescriptorIndexTree.toList =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowDescriptors.toList := by
  rfl

/-- Every natural index has the exact original array value, including the zero default. -/
theorem generatedTenth_root_two_row_descriptor_index_tree_actual (n : ℕ) :
    generatedTenthRootTwoRowDescriptorIndexTree.lookup n =
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowDescriptors[n]?.getD 0 := by
  rw [GeneratedNinthBalancedIndexTree.lookup_eq_list _
    generatedTenth_root_two_row_descriptor_index_tree_valid,
    generatedTenth_root_two_row_descriptor_index_tree_list,
    Array.getElem?_toList]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
