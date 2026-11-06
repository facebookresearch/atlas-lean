/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcSixthW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentRespace

/-! # A kernel-feasible packed Sixth tensor

The packed Sixth tensor `sixthSrcXW w` (worker `gforest`) is defined through the classification
numerators `sixthTNum`; one column at width `88` already needs about 10 GiB of kernel memory.
Here the classification tables are copied literally (each copy certified by one kernel check),
the fast numerator `sixthTNumF` is proved equal to `sixthTNum` symbolically, and the packed
tensor `sixthSXF w` is built from compact literal columns (8-bit fields, re-spaced to width `w` by
`respace`).  One kernel check per compact column certifies its values against
`sixthTNumF`; `respace` keeps the fields, so at every width the tensor `sixthSXF w` has the
rational tensor of `sixthSrcXW w` (`sixthSXF_ten`) and field bound `2 ^ 8 - 1` (`sixthSXF_bnd`). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-! ## Literal tables -/

/-- The Golay codewords of the labels below `2048`, in `24`-bit fields. -/
@[irreducible] def sixthGolayTab : ℕ :=
    0xf000f00f000ffff0f000f00ff0000f0f00f0fff000ff00ff0ff0fff0f0000000 |||
    (0x3c33f0cc330033c3f0333cf0cccc00ffff00000ff000f0f0ff00000f00f0f0 <<< 256) |||
    (0x333300ccc3f0cc3cf033cc00c3ccf03c3c003cc300c333f03cccf0c33c00c3c3 <<< 512) |||
    (0x5a005aa500a555f05aaaf0a55a00a5a5005a55f0aa550055a5f0555af0aaaa00 <<< 768) |||
    (0x9699f06699009969f09996f0666600555500aaa5f0aa5af055aa00a5aaf05a <<< 1024) |||
    (0x9999006669f06696f09966006966f09696009669006999f09666f06996006969 <<< 1280) |||
    (0x30c09acfc0653f309ac0306530c065cfc09a3f306a3fc095cf309530306ac0c0 <<< 1536) |||
    (0xc056f330a6f3c059033059fc30a60cc0953fc06acf306a303095c0c065c0309a <<< 1792) |||
    (0x59f3c0a60330a6fc30590cc0a90c3056fcc05603c0a9f330560c30a9fcc0a903 <<< 2048) |||
    (0x9ac03065c0cf9530306a30cf9ac0cf65c0309530c095c03f65303f9a30c06ac0 <<< 2304) |||
    (0xc0fc59300c59c0f3a930f356300ca6c03f95c0c06530c09a303f6ac0cf6a3030 <<< 2560) |||
    (0xf359c00ca9300c5630f3a6c003a630fc56c0fca9c0035930fca6300356c003a9 <<< 2816) |||
    (0x50a036afa0c95f5036a050c950a0c9afa0365f50c65fa039af50395050c6a0a0 <<< 3072) |||
    (0xa0fa93500a93a0f56350f59c500a6ca0395fa0c6af50c6505039a0a0c9a05036 <<< 3328) |||
    (0xf593a00a63500a9c50f56ca0056c50fa9ca0fa63a0059350fa6c50059ca00563 <<< 3584) |||
    (0xfaa09c05a063f5509c0a5063faa06305a09cf5506cf5a093055093fa506c0aa0 <<< 3840) |||
    (0xa0503950a039a05fc9505f3650a0c6a093f5a06c05506cfa50930aa0630a509c <<< 4096) |||
    (0x5f39a0a0c950a036505fc6a0afc6505036a050c9a0af395050c650af36a0afc9 <<< 4352) |||
    (0x90605c6f60a39f905c6090a39060a36f605c9f90ac9f60536f90539090ac6060 <<< 4608) |||
    (0x609053906053609fa3909f5c9060ac60539f60ac6f90ac9090536060a360905c <<< 4864) |||
    (0x9f536060a390605c909fac606fac90905c6090a3606f539090ac906f5c606fa3 <<< 5120) |||
    (0x3a60f6c560093590f6ca90093a6009c560f63590063560f9c590f93a9006ca60 <<< 5376) |||
    (0x603af990caf96035099035f690ca0660f9356006c590063a90f9ca6009ca90f6 <<< 5632) |||
    (0x35f960ca0990caf690350660c506903af6603a0960c5f9903a0690c5f660c509 <<< 5888) |||
    (0x300c56cf0ca93ffc56c0fca9300ca9cf0c563ffca63f0c59cffc5930fca6c00c <<< 6144) |||
    (0xc9af3fc6af30c9503fc95fcfc6a0c0c593f0ca6cffca630fc59c00ca9c0fc56 <<< 6400) |||
    (0x95f30c6a03fc6afcfc950c0c650cfc9afc0c9a030c65f3fc9a0cfc65fc0c6503 <<< 6656) |||
    (0x9a0cfc650c0395fcfc6afc039a0c03650cfc95fc0c950cf365fcf39afc0c6a0c <<< 6912) |||
    (0xc3059fcc0590c3fa9fc3f56fcc0a60cf3950c0c65fc0c9afcf36a0c036afcfc <<< 7168) |||
    (0x3f590cc0a9fcc056fc3fa60ccfa6fc30560c30a90ccf59fc30a6fccf560ccfa9 <<< 7424) |||
    (0xf0cc3c0fccc3ff3c3c003cc3f0ccc30fcc3cff3cccffcc330f3c33f03ccc00cc <<< 7680) |||
    (0xccf0333c0033ccffc33cff3c3c00cccc33ffcccc0f3cccf03c3300ccc3003c3c <<< 7936) |||
    (0xff33cc00c33c003c3cffcccc0fcc3cf03cccf0c3cc0f333cf0cc3c0f3ccc0fc3 <<< 8192) |||
    (0x5acc96a5cc69553c96aa3c695acc69a5cc96553c6655cc99a53c995a3c66aacc <<< 8448) |||
    (0xcc5a993caa99cc55693c55963caa66cc9955cc66a53c665a3c99aacc69aa3c96 <<< 8704) |||
    (0x5599ccaa693caa963c5566cca5663c5a96cc5a69cca5993c5a663ca596cca569 <<< 8960) |||
    (0x90ac906fac6f9f5c90605c6f90ac6f6fac909f5c609fac9f6f5c9f905c6060ac <<< 9216) |||
    (0xac5c535cac53ac53a35c535c5cacacac9f9fac606f5c60905c9f60ac6f605c90 <<< 9472) |||
    (0x5353acaca35cac5c5c53acaca3ac5c5c5cac5ca3aca3535c5cac5ca35caca3a3 <<< 9728) |||
    (0x3aac3ac5acc5355c3aca5cc53aacc5c5ac3a355cca35ac35c55c353a5ccacaac <<< 9984) |||
    (0xacf6f95c06f9acf9095cf9f65c0606ac3535accac55cca3a5c35caacc5ca5c3a <<< 10240) |||
    (0xf9f9ac06095c06f65cf906ac09065cf6f6acf609ac09f95cf6065c09f6ac0909 <<< 10496) |||
    (0x506cfaaf6c055f9cfaa09c05506c05af6cfa5f9c0a5f6cf5af9cf5509c0aa06c <<< 10752) |||
    (0x6c36939cc6936c39639c399c9cc66c6cf55f6c0aaf9c0a509cf5a06c05a09cfa <<< 11008) |||
    (0x39936cc6639cc69c9c396c6cc96c9c369c6c36636cc9939c366c9cc99c6cc963 <<< 11264) |||
    (0xfa6c50056caff59c500a9caffa6caf056c50f59ca0f56c5f059c5ffa9ca00a6c <<< 11520) |||
    (0x6c9c399c6c396c93c99c93369c6cc66c5ff56ca0059ca0fa9c5f0a6caf0a9c50 <<< 11776) |||
    (0x93396c6cc99c6c369c93c66c63c69c9c366c9cc96c63399c9cc69c63366c63c9 <<< 12032) |||
    (0x500a9caf0a635ffa9ca0fa63500a63af0a9c5ffa6c5f0a93affa9350fa6ca00a <<< 12288) |||
    (0xa5093faa0930a5f63fa5f9cfaa06c0a935f0a6caffa6c50fa93a00a63a0fa9c <<< 12544) |||
    (0x5f930aa063faa09cfa5f6c0aaf6cfa509c0a50630aaf93fa506cfaaf9c0aaf63 <<< 12800) |||
    (0xfa0a36050ac9f5fa360afac9fa0ac9050a36f5fac6f50a3905fa39fafac60a0a <<< 13056) |||
    (0xafa39fa0a390af5c9faf536fa0ac60a39f50ac605fac6fafa390a0ac90afa36 <<< 13312) |||
    (0xf5390a0ac9fa0a36faf5c60a05c6fafa360afac90a0539fafac6fa05360a05c9 <<< 13568) |||
    (0x90caf66fca099f3af6603a0990ca096fcaf69f3a069fcaf96f3af9903a0660ca <<< 13824) |||
    (0xca3a533aca53ca35a33a355c3acaaccaf99fca066f3a06903af960ca09603af6 <<< 14080) |||
    (0x3553cacaa33aca5c3a35accac5ac3a3a5cca3aa3cac5533a3aac3ac55ccac5a3 <<< 14336) |||
    (0x3aca5cc5caa3353a5cca3aa33acaa3c5ca5c353aac35ca53c53a533a3aaccaca <<< 14592) |||
    (0xca90f93a60f9ca9f093a9ff63a6006ca5335caacc53aac3a3a53cacaa3ca3a5c <<< 14848) |||
    (0x9ff9ca60093a60f63a9f06ca6f063a90f6ca9009ca6ff93a90063a6ff6ca6f09 <<< 15104) |||
    (0xf0aa5a0faaa5ff5a5a005aa5f0aaa50faa5aff5aaaffaa550f5a55f05aaa00aa <<< 15360) |||
    (0xaa96335a6633aa99c35a993c5a66ccaa55ffaaaa0f5aaaf05a5500aaa5005a5a <<< 15616) |||
    (0x9933aa66c35a663c5a99ccaa69cc5a963caa96c3aa69335a96cc5a693caa69c3 <<< 15872) |||
    (0x5aaaf0a5aa0f555af0aa5a0f5aaa0fa5aaf0555a0055aaffa55aff5a5a00aaaa <<< 16128) |||
    (0xaa3c995acc99aa33695a33965acc66aaff55aa00a55a005a5affaaaa0faa5af0 <<< 16384) |||
    (0x3399aacc695acc965a3366aac3665a3c96aa3c69aac3995a3c665ac396aac369 <<< 16640) |||
    (0x306a30cf6acf3f9a30c09acf306acfcf6a303f9ac03f6a3fcf9a3f309ac0c06a <<< 16896) |||
    (0x6afcf39a0cf36af3039af3fc9a0c0c6a3f3f6ac0cf9ac0309a3fc06acfc09a30 <<< 17152) |||
    (0xf3f36a0c039a0cfc9af30c6a030c9afcfc6afc036a03f39afc0c9a03fc6a0303 <<< 17408) |||
    (0x9a6a9a656a65959a9a6a9a659a6a65656a9a959a6a956a95659a959a9a6a6a6a <<< 17664) |||
    (0x6a56599aa6596a59a99a59569aa6a66a95956a6a659a6a9a9a956a6a656a9a9a <<< 17920) |||
    (0x59596aa6a99aa6569a59a66aa9a69a56566a56a96aa9599a56a69aa9566aa9a9 <<< 18176) |||
    (0x90063a6f06c59ff63a60f6c59006c56f063a9ff6ca9f06356ff63590f6ca6006 <<< 18432) |||
    (0x6f653f6065306f9a3f6f95cf606ac06359f06ca6ff6ca90f6356006c560f63a <<< 18688) |||
    (0xf9530606a3f6065cf6f9ac0609acf6f65c06f6a3060953f6f6acf6095c0609a3 <<< 18944) |||
    (0x3a0690c5066f35f690caf66f3a066fc5069035f66035069fc5f69f3af660ca06 <<< 19200) |||
    (0x65cf9f6acf9065309f653f6f6ac06069f350660c5f6603af69fca066fcaf690 <<< 19456) |||
    (0x53f906ac09f6acf6f6530606a306f65cf6065c0906a3f9f65c06f6a3f606a309 <<< 19712) |||
    (0x50c650afc6af5f3650a036af50c6afafc6505f36a05fc65faf365f5036a0a0c6 <<< 19968) |||
    (0xc69c93366c93c6936336939c366c6cc65f5fc6a0af36a050365fa0c6afa03650 <<< 20224) |||
    (0x9393c66c63366c9c36936cc6636c369c9cc69c63c66393369c6c36639cc66363 <<< 20480) |||
    (0xfac6fa05c605f536fa0a3605fac60505c6faf5360af5c6f50536f5fa360a0ac6 <<< 20736) |||
    (0xc6363936c639c639c936393636c6c6c6f5f5c60a05360afa36f50ac6050a36fa <<< 20992) |||
    (0x3939c6c6c936c6363639c6c6c9c6363636c636c9c6c9393636c636c936c6c9c9 <<< 21248) |||
    (0x30a6fccfa6033f56fcc0560330a603cfa6fc3f560c3fa6f3cf56f330560cc0a6 <<< 21504) |||
    (0xa630f356c0f3a63f03563ffc56c00ca6f33fa60ccf560c3056f3c0a603c056fc <<< 21760) |||
    (0x3ff3a6c00356c0fc563f0ca6cf0c5630fca63003a6cff356300c56cffca6cf03 <<< 22016) |||
    (0x9aa65665a6a99556566a56a99aa6a965a6569556a695a6596556599a56a66aa6 <<< 22272) |||
    (0xa69a59566a59a695a9569556566aa6a65995a6a66556a69a56596aa6a96a5656 <<< 22528) |||
    (0x9559a66aa9566a565695a6a665a6569a56a69aa9a66559569aa6566556a665a9 <<< 22784) |||
    (0xf066960f6669ff9696009669f066690f6696ff9666ff66990f9699f096660066 <<< 23040) |||
    (0x665a3396aa336655c396553c96aacc6699ff66660f9666f09699006669009696 <<< 23296) |||
    (0x553366aac396aa3c9655cc66a5cc965a3c665ac366a533965acc96a53c66a5c3 <<< 23552) |||
    (0x5a663ca566c355963caa96c35a66c3a5663c5596cc556633a596335a96ccaa66 <<< 23808) |||
    (0x66f09996009966ff6996ff9696006666335566cca596cc5a9633aa66c3aa963c <<< 24064) |||
    (0xff9966006996009696ff66660f6696f09666f069660f9996f066960f96660f69 <<< 24320) |||
    (0xe11ee11e1e1eeeeee111ee1ee11e1e1e1ee1eeee11ee1eee1eeeeee1ee11111e <<< 24576) |||
    (0x1e2d22eedd221e22d2ee222deedddd1eeeee1e111eee11e1eeee111e1e11eee1 <<< 24832) |||
    (0x22221eddd2eedd2dee22dd1ed2ddee2d2d1e2dd21ed222ee2dddeed22d1ed2d2 <<< 25088) |||
    (0x4b1e4bb41eb444ee4bbbeeb44b1eb4b41e4b44eebb441e44b4ee444beebbbb1e <<< 25344) |||
    (0x1e8788ee77881e8878ee8887ee77771e44441ebbb4eebb4bee44bb1eb4bbee4b <<< 25600) |||
    (0x88881e7778ee7787ee88771e7877ee87871e87781e7888ee8777ee78871e7878 <<< 25856) |||
    (0x21de8bdede742e2e8bd12e7421de74dede8b2e2e7b2ede84de2e84212e7bd1de <<< 26112) |||
    (0xde47e22eb7e2de48122e48ed2eb71dde842ede7bde2e7b212e84d1de74d12e8b <<< 26368) |||
    (0x48e2deb7122eb7ed2e481ddeb81d2e47edde4712deb8e22e471d2eb8eddeb812 <<< 26624) |||
    (0x8bde2174dede842e217b2ede8bdede74de21842ed184de2e742e2e8b2ed17bde <<< 26880) |||
    (0xdeed482e1d48dee2b82ee2472e1db7de2e84ded1742ed18b2e2e7bdede7b2e21 <<< 27136) |||
    (0xe248de1db82e1d472ee2b7de12b72eed47deedb8de12482eedb72e1247de12b8 <<< 27392) |||
    (0x41be27bebed84e4e27b14ed841bed8bebe274e4ed74ebe28be4e28414ed7b1be <<< 27648) |||
    (0xbeeb824e1b82bee4724ee48d4e1b7dbe284ebed7be4ed7414e28b1bed8b14e27 <<< 27904) |||
    (0xe482be1b724e1b8d4ee47dbe147d4eeb8dbeeb72be14824eeb7d4e148dbe1472 <<< 28160) |||
    (0xebbe8d14be72e44e8d1b4e72ebbe7214be8de44e7de4be82144e82eb4e7d1bbe <<< 28416) |||
    (0xbe41284eb128be4ed84e4e274eb1d7be82e4be7d144e7deb4e821bbe721b4e8d <<< 28672) |||
    (0x4e28beb1d84eb1274e4ed7bebed74e4127be41d8bebe284e41d74ebe27bebed8 <<< 28928) |||
    (0x817e4d7e7eb28e8e4d718eb2817eb27e7e4d8e8ebd8e7e427e8e42818ebd717e <<< 29184) |||
    (0x7e81428e71427e8eb28e8e4d8e71bd7e428e7ebd7e8ebd818e42717eb2718e4d <<< 29440) |||
    (0x8e427e71b28e714d8e8ebd7e7ebd8e814d7e81b27e7e428e81bd8e7e4d7e7eb2 <<< 29696) |||
    (0x2b7ee7d47e18248ee7db8e182b7e18d47ee7248e17247ee8d48ee82b8e17db7e <<< 29952) |||
    (0x7e2be88edbe87e24188e24e78edb177ee8247e17d48e172b8ee8db7e18db8ee7 <<< 30208) |||
    (0x24e87edb188edbe78e24177ed4178e2be77e2b187ed4e88e2b178ed4e77ed418 <<< 30464) |||
    (0x211247de12b82ee247d1e2b82112b8de12472ee2b72e1248dee24821e2b7d112 <<< 30720) |||
    (0x128be2e27be2128412e284ede27b1d12482e12b7dee2b721e248d112b8d1e247 <<< 30976) |||
    (0x84e2127b12e27bede2841d12741de28bed128b121274e2e28b1de274ed127412 <<< 31232) |||
    (0x8b12ed74121284e2ed7be2128b12127412ed84e21d8412e274e2e28be21d7b12 <<< 31488) |||
    (0x122148e2d148122eb8e22e47e2d1b712e284121d74e21d8be2e27b12127be2ed <<< 31744) |||
    (0x2e4812d1b8e2d147e22eb712deb7e221471221b812de48e221b7e2de4712deb8 <<< 32000) |||
    (0xe1d22d1ed2d2ee222d1122d2e1d2d21ed22dee22ddeed2221e2222e122dd11d2 <<< 32256) |||
    (0xd2e122221122d2eed222ee2d2211ddd222eed2dd1e22dde1222211d2d211222d <<< 32512) |||
    (0xee22d211d222112d22eeddd21edd22e12dd2e1d2d21e2222e1dd221e2dd21ed2 <<< 32768) |||
    (0x4bd287b4d278442287bb22784bd278b4d28744227744d288b422884b2277bbd2 <<< 33024) |||
    (0xd24b8822bb88d2447822448722bb77d28844d277b422774b2288bbd278bb2287 <<< 33280) |||
    (0x4488d2bb7822bb87224477d2b477224b87d24b78d2b488224b7722b487d2b478 <<< 33536) |||
    (0x81b2817eb27e8e428171427e81b27e7eb2818e42718eb28e7e428e81427171b2 <<< 33792) |||
    (0xb24d4242bd42b242b242424d42bdbdb28e8eb2717e427181428e71b27e714281 <<< 34048) |||
    (0x4242b2bdb242bd4d4242bdb2b2bd424d4db24db2b2b242424dbd42b24db2b2b2 <<< 34304) |||
    (0x2bb22bd4b2d424422bdb42d42bb2d4d4b22b2442db24b224d442242b42dbdbb2 <<< 34560) |||
    (0xb2e7e84217e8b2e81842e8e7421717b22424b2dbd442db2b4224dbb2d4db422b <<< 34816) |||
    (0xe8e8b217184217e742e817b2181742e7e7b2e718b218e842e7174218e7b21818 <<< 35072) |||
    (0x4172ebbe72144e82ebb18214417214be72eb4e821b4e72e4be82e441821bb172 <<< 35328) |||
    (0x72278282d78272287282288d82d77d72e44e721bbe821b4182e4b17214b182eb <<< 35584) |||
    (0x288272d77282d78d82287d72d87d82278d72277272d88282277d82d88d72d872 <<< 35840) |||
    (0xeb72411472bee482411b82beeb72be147241e482b1e4724e14824eeb82b11b72 <<< 36096) |||
    (0x728d28827d287282d8828227827dd7724ee472b11482b1eb824e1b72be1b8241 <<< 36352) |||
    (0x8228727dd8827d278282d77272d7828d27728dd8727228828dd78272277272d8 <<< 36608) |||
    (0x41148dbe14724ee48db1e472411472be148d4ee47d4e1482bee48241e47db114 <<< 36864) |||
    (0x144182e4b182144e72e44e8de4b17d14824e147dbee47d41e482b11472b1e48d <<< 37120) |||
    (0x4e8214b172e4b18de44e7d14be7de4418d14417214be82e4417de4be8d14be72 <<< 37376) |||
    (0xeb14271414d8e4e4271be4d8eb14d8141427e4e4d7e4142814e428ebe4d71b14 <<< 37632) |||
    (0x14eb28e41b2814e4d8e4e427e41bd71428e414d714e4d7ebe4281b14d81be427 <<< 37888) |||
    (0xe428141bd8e41b27e4e4d71414d7e4eb2714ebd8141428e4ebd7e414271414d8 <<< 38144) |||
    (0x81d4e77ed4188e24e771241881d4187ed4e78e24178ed4e87e24e881241771d4 <<< 38400) |||
    (0xd42b4224db42d424b224244d24dbbdd4e88ed4177e24178124e871d4187124e7 <<< 38656) |||
    (0x2442d4dbb224db4d2424bdd4d4bd242b4dd42bb2d4d442242bbd24d44dd4d4b2 <<< 38912) |||
    (0x2bd44dd4d4b224244ddb24b22bd4b2d4d44d2424bd24d442d424422b24bddbd4 <<< 39168) |||
    (0xd481e82471e8d48e18248ee7247117d44224d4bdd424bd2b2442dbd4b2db244d <<< 39424) |||
    (0x8ee8d471182471e7248e17d47e172481e7d48118d47ee8248117247ee7d47e18 <<< 39680) |||
    (0xe1b44b1eb4b4ee444b1144b4e1b4b41eb44bee44bbeeb4441e4444e144bb11b4 <<< 39936) |||
    (0xb48722447722b488d244882d4477ddb444eeb4bb1e44bbe1444411b4b411444b <<< 40192) |||
    (0x8822b477d244772d4488ddb478dd44872db487d2b478224487dd44782db478d2 <<< 40448) |||
    (0x4bb4e1b4b41e4444e1bb441e4bb41eb4b4e144441144b4eeb444ee4b4411bbb4 <<< 40704) |||
    (0xb42d8844dd88b4227844228744dd77b4ee44b411b444114b44eebbb41ebb44e1 <<< 40960) |||
    (0x2288b4dd7844dd87442277b4d277442d87b42d78b4d288442d7744d287b4d278 <<< 41216) |||
    (0x217421de74de2e8421d184de2174dede74212e84d12e742ede842e2184d1d174 <<< 41472) |||
    (0x74ede2841de274e21284e2ed841d1d742e2e74d1de84d121842ed174ded18421 <<< 41728) |||
    (0xe2e2741d12841ded84e21d74121d84eded74ed127412e284ed1d8412ed741212 <<< 41984) |||
    (0x8b748b74747484848b7b84748b747474748b84847b8474847484848b847b7b74 <<< 42240) |||
    (0x74474884b7487448b884484784b7b7748484747b74847b8b84847b74747b848b <<< 42496) |||
    (0x484874b7b884b7478448b774b8b78447477447b874b8488447b784b84774b8b8 <<< 42752) |||
    (0x81182b7e18d48ee82b71e8d48118d47e182b8ee8db8e18247ee82481e8db7118 <<< 43008) |||
    (0x18e742e8174218e8b2e8e84de817bd18248e18db7ee8db81e8247118d471e82b <<< 43264) |||
    (0xe8421817b2e8174de8e8bd1818bde8e74d18e7b2181842e8e7bde8184d1818b2 <<< 43520) |||
    (0x2b1881d4187e24e881dbe87e2b187ed4188124e87124188ed4e88e2be871db18 <<< 43776) |||
    (0x184de8e8bde8184218e842e7e8bd17188e241871d4e8712be88edb187edbe881 <<< 44032) |||
    (0x42e818bd18e8bde7e8421718b217e84de7184d1818b2e8e84d17e8b2e718b218 <<< 44288) |||
    (0x41d841bed8be4e2841b128be41d8bebed8414e28b14ed84ebe284e4128b1b1d8 <<< 44544) |||
    (0xd88d82287d82d8827228828d287d7dd84e4ed8b1be28b141284eb1d8beb12841 <<< 44800) |||
    (0x8282d87d72287d8d28827dd8727d288d8dd88d72d87282288d7d28728dd87272 <<< 45056) |||
    (0xebd8eb14d814e428eb1b2814ebd81414d8ebe4281be4d8e41428e4eb281b1bd8 <<< 45312) |||
    (0xd8272828d728d828d828282728d7d7d8e4e4d81b14281beb28e41bd8141b28eb <<< 45568) |||
    (0x2828d8d7d828d7272828d7d8d8d7282727d827d8d8d8282827d728d827d8d8d8 <<< 45824) |||
    (0x21b8eddeb8122e48edd1481221b812deb8ed2e481d2eb8e2de48e221481dd1b8 <<< 46080) |||
    (0xb821e248d1e2b82e12482eed48d11db8e22eb81dde481d2148e2d1b812d148ed <<< 46336) |||
    (0x2ee2b8d11248d1ed482e1db8de1d4821edb82112b8dee248211d48deedb8de12 <<< 46592) |||
    (0x8bb84774b8b88448477b48b88bb8b874b8478448b784b8487448488b48b77bb8 <<< 46848) |||
    (0xb88b48487b48b884b8488447487bb7b84884b8b77448b78b48487bb8b87b4847 <<< 47104) |||
    (0x8448b87bb8487b474884b7b874b7488b47b88bb8b87448488bb7487447b874b8 <<< 47360) |||
    (0xe178871e7878ee8887118878e178781e7887ee8877ee78881e8888e188771178 <<< 47616) |||
    (0x784b2288bb227844d288442d88bbdd7888ee78771e8877e18888117878118887 <<< 47872) |||
    (0x442278bbd288bb2d8844dd78b4dd884b2d784bd278b422884bdd88b42d78b4d2 <<< 48128) |||
    (0x4b782db478d244882dbb88d24b78d2b4782d4488dd447822b488224b88ddbb78 <<< 48384) |||
    (0x78e18888118878ee7888ee8788117778224478ddb488dd4b8822bb78d2bb882d <<< 48640) |||
    (0xee8878117888118788ee77781e7788e18778e178781e8888e177881e87781e78 <<< 48896)

/-- The weight-class bits: bit `d` is the parity of a quarter of the weight of codeword `d`. -/
@[irreducible] def sixthWSignTab : ℕ :=
    0xa55a96969966c33c9966a55a9696c33c96969966a55ac33c6996699669960000 |||
    (0xffff3c3cffff55aa33ccffffffff5a5affffffff0ff06666f0f0ff00ccccaaaa <<< 256) |||
    (0xffffffff33cc5a5affff0ff0ffff66663c3cffffffff55aaff00ccccf0f0aaaa <<< 512) |||
    (0xff0ffffffff6666ffffffff3c3c55aaffff33ccffff5a5accccf0f0ff00aaaa <<< 768) |||
    (0xdbb2e87ee78ebdd4e78edbb2e87ebdd4e87ee78edbb2bdd4177e177e177e7ee8 <<< 1024) |||
    (0x7ee8bd2b7ee8d4bdb2db7ee87ee8db4d7ee87ee88ee7e77171e77e174ddb2bbd <<< 1280) |||
    (0x7ee87ee8b2dbdb4d7ee88ee77ee8e771bd2b7ee87ee8d4bd7e174ddb71e72bbd <<< 1536) |||
    (0x8ee77ee87ee8e7717ee87ee8bd2bd4bd7ee8b2db7ee8db4d4ddb71e77e172bbd <<< 1792)

/-- The positive odd-numerator mask of column `0`. -/
@[irreducible] def sixthPosM0 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x220000880000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x20000000000800000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `1`. -/
@[irreducible] def sixthPosM1 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x8800000000000000000000000000004400000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x800000000000000000000000000000000000000000000800000000000000 <<< 1536)

/-- The positive odd-numerator mask of column `2`. -/
@[irreducible] def sixthPosM2 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x22000000000000000000440000000000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x40000000000000000000000000000000000040000 <<< 1280)

/-- The positive odd-numerator mask of column `3`. -/
@[irreducible] def sixthPosM3 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x44000000000000000011000000110000000000 <<< 768) |||
    (0x1000000000000000000000000100000000000000000000040000000400000000 <<< 1024)

/-- The positive odd-numerator mask of column `4`. -/
@[irreducible] def sixthPosM4 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x801000000000000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x8000000000000000000000000000000000000000000000000000000000000 <<< 1024) |||
    (0x400000000000000000000000000000000000000000000000000 <<< 1280)

/-- The positive odd-numerator mask of column `5`. -/
@[irreducible] def sixthPosM5 : ℕ :=
    0x0 |||
    (0x10800000000000000000000000000000000000000000000000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x80000000000000000000000000000000000000 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x200000000000000000000000000000000000 <<< 1536)

/-- The positive odd-numerator mask of column `6`. -/
@[irreducible] def sixthPosM6 : ℕ :=
    0x4020000000000000000000000000000000000000000000000000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x20000000000000000000 <<< 1024) |||
    (0x40000000000000000000000000000000 <<< 1280) |||
    (0x200000000000000000000000 <<< 1536) |||
    (0x20000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `7`. -/
@[irreducible] def sixthPosM7 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x20000000 <<< 1280) |||
    (0x10000000000000 <<< 1536)

/-- The positive odd-numerator mask of column `8`. -/
@[irreducible] def sixthPosM8 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x84000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x2000000000000000000000000000000000000000000000000000000000000000 <<< 1024) |||
    (0x10000000000000000000000000000 <<< 1280)

/-- The positive odd-numerator mask of column `9`. -/
@[irreducible] def sixthPosM9 : ℕ :=
    0x840000000000000000000000000000000000000000000000 |||
    (0x8400000000000000 <<< 256) |||
    (0x840000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x800000000 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x800000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `10`. -/
@[irreducible] def sixthPosM10 : ℕ :=
    0x0 |||
    (0x2100000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x200000000000000000000000000000000000000 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x800000000000000000000 <<< 1536)

/-- The positive odd-numerator mask of column `11`. -/
@[irreducible] def sixthPosM11 : ℕ :=
    0x0 |||
    (0x84000000000000 <<< 256) |||
    (0x210000000000000000000000000000 <<< 512)

/-- The positive odd-numerator mask of column `12`. -/
@[irreducible] def sixthPosM12 : ℕ :=
    0x0 |||
    (0x2800000000000000000000000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x200000000000000000000000000000000000000000000000000000000000 <<< 1536)

/-- The positive odd-numerator mask of column `13`. -/
@[irreducible] def sixthPosM13 : ℕ :=
    0x28000000000000000000000000 |||
    (0x1400000000000000000000000000000000 <<< 256) |||
    (0x280000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x200000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `14`. -/
@[irreducible] def sixthPosM14 : ℕ :=
    0x2800000000000000000000000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x10000000000000000000000000000000000000000 <<< 1280) |||
    (0x200000000000000 <<< 1536) |||
    (0x80000000000000000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `15`. -/
@[irreducible] def sixthPosM15 : ℕ :=
    0x14000000000000000000000000 |||
    (0x140000000000000000000000000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x4000000000000000000000000000000000000000000000000000000000000000 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x100000000000000000000000000000000 <<< 1536) |||
    (0x100000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `16`. -/
@[irreducible] def sixthPosM16 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x4000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x400000000000000000000000000000000000400000 <<< 1280) |||
    (0x80000000000000000000000000000000000000000008000000000000000 <<< 1536) |||
    (0x2000000008000000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `17`. -/
@[irreducible] def sixthPosM17 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x4000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x400000000000000000000000000000000000400000 <<< 1280) |||
    (0x80000000000000000000000000000000000000000008000000000000000 <<< 1536) |||
    (0x2000000008000000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `18`. -/
@[irreducible] def sixthPosM18 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0xbd2b000000000000000000000000000000000000000000000000000000000000 <<< 768)

/-- The positive odd-numerator mask of column `19`. -/
@[irreducible] def sixthPosM19 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x42d0000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x100000000000000000000001000000000000000000000400000004000000000 <<< 1024) |||
    (0x2000000000000000000200000000000000000000000000000 <<< 1280) |||
    (0x4000000000004000000000000000000000 <<< 1536) |||
    (0x4000000000000000000000000010 <<< 1792)

/-- The positive odd-numerator mask of column `20`. -/
@[irreducible] def sixthPosM20 : ℕ :=
    0x1001 |||
    (0x0 <<< 256) |||
    (0x80080000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x1000000000000000000000000000000000000 <<< 1024) |||
    (0x2000000000000000000000000000000000000000000000000000 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x4000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `21`. -/
@[irreducible] def sixthPosM21 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x10010000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x4000000000000000000000000000000000000000000 <<< 1280)

/-- The positive odd-numerator mask of column `22`. -/
@[irreducible] def sixthPosM22 : ℕ :=
    0x2002 |||
    (0x400400000000000000000000 <<< 256) |||
    (0x20020000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x200000000000000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator mask of column `23`. -/
@[irreducible] def sixthPosM23 : ℕ :=
    0x8008 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x4000000 <<< 1280) |||
    (0x8000000000000000000000000000000000000000000000000000000000 <<< 1536) |||
    (0x80000000000000000000000000000000000000000000000 <<< 1792)

/-- The positive odd-numerator masks. -/
def sixthPosM : List ℕ :=
  [sixthPosM0, sixthPosM1, sixthPosM2, sixthPosM3, sixthPosM4, sixthPosM5, sixthPosM6,
    sixthPosM7, sixthPosM8, sixthPosM9, sixthPosM10, sixthPosM11, sixthPosM12, sixthPosM13,
    sixthPosM14, sixthPosM15, sixthPosM16, sixthPosM17, sixthPosM18, sixthPosM19, sixthPosM20,
    sixthPosM21, sixthPosM22, sixthPosM23]

/-- The negative odd-numerator mask of column `0`. -/
@[irreducible] def sixthNegM0 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1100000000000000000000000000000000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x400000000000000000000000001 <<< 1792)

/-- The negative odd-numerator mask of column `1`. -/
@[irreducible] def sixthNegM1 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x88000000000000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x400000000000400000000000000000000 <<< 1536)

/-- The negative odd-numerator mask of column `2`. -/
@[irreducible] def sixthNegM2 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x2200000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x20000000000000000000020000000000000000000000000000 <<< 1280)

/-- The negative odd-numerator mask of column `3`. -/
@[irreducible] def sixthNegM3 : ℕ :=
    0

/-- The negative odd-numerator mask of column `4`. -/
@[irreducible] def sixthNegM4 : ℕ :=
    0x1080000000000000000000000000000000000000000000000000000 |||
    (0x40200000000000000000000000000000000000000000000000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x100000000000000000000000000000000000000000000000000000000 <<< 1536) |||
    (0x40000000000000000000000000000000000000000000000000000 <<< 1792)

/-- The negative odd-numerator mask of column `5`. -/
@[irreducible] def sixthNegM5 : ℕ :=
    0x2040000000000000000000000000000000000000000000000000000 |||
    (0x0 <<< 256) |||
    (0x108000000000000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x20000000000000000000000000000000000000000000 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x100000000000000000000000000000000000000000000000 <<< 1792)

/-- The negative odd-numerator mask of column `6`. -/
@[irreducible] def sixthNegM6 : ℕ :=
    0x0 |||
    (0x20400000000000000000000000000000000000000000000000000000000 <<< 256) |||
    (0x402000000000000000000000000000000000000000000000000 <<< 512)

/-- The negative odd-numerator mask of column `7`. -/
@[irreducible] def sixthNegM7 : ℕ :=
    0x8010000000000000000000000000000000000000000000000000000 |||
    (0x80100000000000000000000000000000000000000000000000000000000 <<< 256) |||
    (0x204000000000000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x200000000000 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x8000 <<< 1792)

/-- The negative odd-numerator mask of column `8`. -/
@[irreducible] def sixthNegM8 : ℕ :=
    0x210000000000000000000000000000000000000000000000 |||
    (0x21000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x400000000000000 <<< 1536) |||
    (0x400000000000000000000000000000000000000000000 <<< 1792)

/-- The negative odd-numerator mask of column `9`. -/
@[irreducible] def sixthNegM9 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x80000000000000000000000000000000000000000 <<< 1280) |||
    (0x400000000000000000000000000000000000000000000000000000000000 <<< 1536)

/-- The negative odd-numerator mask of column `10`. -/
@[irreducible] def sixthNegM10 : ℕ :=
    0x8400000000000000000000000000000000000000000000 |||
    (0x0 <<< 256) |||
    (0x21000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x80000 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x10000000000000000000000000000000000000000000000000000000 <<< 1792)

/-- The negative odd-numerator mask of column `11`. -/
@[irreducible] def sixthNegM11 : ℕ :=
    0x2100000000000000000000000000000000000000000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x80000000000000000 <<< 1024) |||
    (0x10000000000000000000000000000000000000000000000000 <<< 1280) |||
    (0x800000000000000000000000000000000 <<< 1536) |||
    (0x2 <<< 1792)

/-- The negative odd-numerator mask of column `12`. -/
@[irreducible] def sixthNegM12 : ℕ :=
    0x1400000000000000000000000000 |||
    (0x0 <<< 256) |||
    (0x28000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x400000000000000000000000000000000000000 <<< 1024) |||
    (0x80000000000000000000000000000 <<< 1280) |||
    (0x0 <<< 1536) |||
    (0x4 <<< 1792)

/-- The negative odd-numerator mask of column `13`. -/
@[irreducible] def sixthNegM13 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x100000000 <<< 1024) |||
    (0x80000000000000000000000000000000000000000000000000 <<< 1280) |||
    (0x100000000000000000000 <<< 1536)

/-- The negative odd-numerator mask of column `14`. -/
@[irreducible] def sixthNegM14 : ℕ :=
    0x0 |||
    (0x280000000000000000000000000000000000 <<< 256) |||
    (0x140000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x10000000000000000 <<< 1024)

/-- The negative odd-numerator mask of column `15`. -/
@[irreducible] def sixthNegM15 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x14000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x10000 <<< 1280)

/-- The negative odd-numerator mask of column `16`. -/
@[irreducible] def sixthNegM16 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x42d0000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x100000000000000000000001000000000000000000000400000004000000000 <<< 1024) |||
    (0x2000000000000000000200000000000000000000000000000 <<< 1280) |||
    (0x4000000000004000000000000000000000 <<< 1536) |||
    (0x4000000000000000000000000010 <<< 1792)

/-- The negative odd-numerator mask of column `17`. -/
@[irreducible] def sixthNegM17 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x42d0000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x100000000000000000000001000000000000000000000400000004000000000 <<< 1024) |||
    (0x2000000000000000000200000000000000000000000000000 <<< 1280) |||
    (0x4000000000004000000000000000000000 <<< 1536) |||
    (0x4000000000000000000000000010 <<< 1792)

/-- The negative odd-numerator mask of column `18`. -/
@[irreducible] def sixthNegM18 : ℕ :=
    0

/-- The negative odd-numerator mask of column `19`. -/
@[irreducible] def sixthNegM19 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x4000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x400000000000000000000000000000000000400000 <<< 1280) |||
    (0x80000000000000000000000000000000000000000008000000000000000 <<< 1536) |||
    (0x2000000008000000000000000000000000000000000000000000000 <<< 1792)

/-- The negative odd-numerator mask of column `20`. -/
@[irreducible] def sixthNegM20 : ℕ :=
    0x0 |||
    (0x200200000000000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x8000000000000 <<< 1536)

/-- The negative odd-numerator mask of column `21`. -/
@[irreducible] def sixthNegM21 : ℕ :=
    0x4004 |||
    (0x100100000000000000000000 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x10000000000000000000000000000000000000000000000000000000000000 <<< 1024) |||
    (0x0 <<< 1280) |||
    (0x40000000000000000000000 <<< 1536) |||
    (0x100 <<< 1792)

/-- The negative odd-numerator mask of column `22`. -/
@[irreducible] def sixthNegM22 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x0 <<< 768) |||
    (0x40000000000 <<< 1024) |||
    (0x2000000000000000000000000000000 <<< 1280) |||
    (0x40000000000000000000000000000000000 <<< 1536)

/-- The negative odd-numerator mask of column `23`. -/
@[irreducible] def sixthNegM23 : ℕ :=
    0x0 |||
    (0x800800000000000000000000 <<< 256) |||
    (0x40040000000000000000000000000000000000000000 <<< 512) |||
    (0x0 <<< 768) |||
    (0x4000000000000000000 <<< 1024)

/-- The negative odd-numerator masks. -/
def sixthNegM : List ℕ :=
  [sixthNegM0, sixthNegM1, sixthNegM2, sixthNegM3, sixthNegM4, sixthNegM5, sixthNegM6,
    sixthNegM7, sixthNegM8, sixthNegM9, sixthNegM10, sixthNegM11, sixthNegM12, sixthNegM13,
    sixthNegM14, sixthNegM15, sixthNegM16, sixthNegM17, sixthNegM18, sixthNegM19, sixthNegM20,
    sixthNegM21, sixthNegM22, sixthNegM23]

/-- The high odd-numerator mask of column `0`. -/
@[irreducible] def sixthHighM0 : ℕ :=
    0

/-- The high odd-numerator mask of column `1`. -/
@[irreducible] def sixthHighM1 : ℕ :=
    0

/-- The high odd-numerator mask of column `2`. -/
@[irreducible] def sixthHighM2 : ℕ :=
    0

/-- The high odd-numerator mask of column `3`. -/
@[irreducible] def sixthHighM3 : ℕ :=
    0

/-- The high odd-numerator mask of column `4`. -/
@[irreducible] def sixthHighM4 : ℕ :=
    0

/-- The high odd-numerator mask of column `5`. -/
@[irreducible] def sixthHighM5 : ℕ :=
    0

/-- The high odd-numerator mask of column `6`. -/
@[irreducible] def sixthHighM6 : ℕ :=
    0

/-- The high odd-numerator mask of column `7`. -/
@[irreducible] def sixthHighM7 : ℕ :=
    0

/-- The high odd-numerator mask of column `8`. -/
@[irreducible] def sixthHighM8 : ℕ :=
    0

/-- The high odd-numerator mask of column `9`. -/
@[irreducible] def sixthHighM9 : ℕ :=
    0

/-- The high odd-numerator mask of column `10`. -/
@[irreducible] def sixthHighM10 : ℕ :=
    0

/-- The high odd-numerator mask of column `11`. -/
@[irreducible] def sixthHighM11 : ℕ :=
    0

/-- The high odd-numerator mask of column `12`. -/
@[irreducible] def sixthHighM12 : ℕ :=
    0

/-- The high odd-numerator mask of column `13`. -/
@[irreducible] def sixthHighM13 : ℕ :=
    0

/-- The high odd-numerator mask of column `14`. -/
@[irreducible] def sixthHighM14 : ℕ :=
    0

/-- The high odd-numerator mask of column `15`. -/
@[irreducible] def sixthHighM15 : ℕ :=
    0

/-- The high odd-numerator mask of column `16`. -/
@[irreducible] def sixthHighM16 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x4000000000000000000000000000000000000000000000000000000000000 <<< 768)

/-- The high odd-numerator mask of column `17`. -/
@[irreducible] def sixthHighM17 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x4000000000000000000000000000000000000000000000000000000000000 <<< 768)

/-- The high odd-numerator mask of column `18`. -/
@[irreducible] def sixthHighM18 : ℕ :=
    0

/-- The high odd-numerator mask of column `19`. -/
@[irreducible] def sixthHighM19 : ℕ :=
    0x0 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x42d0000000000000000000000000000000000000000000000000000000000000 <<< 768) |||
    (0x100000000000000000000001000000000000000000000400000004000000000 <<< 1024) |||
    (0x2000000400000000000200000000000000000000000400000 <<< 1280) |||
    (0x80000000000000000000000004000000000004000008000000000000000 <<< 1536) |||
    (0x2000000008000000000000000004000000000000000000000000010 <<< 1792)

/-- The high odd-numerator mask of column `20`. -/
@[irreducible] def sixthHighM20 : ℕ :=
    0

/-- The high odd-numerator mask of column `21`. -/
@[irreducible] def sixthHighM21 : ℕ :=
    0

/-- The high odd-numerator mask of column `22`. -/
@[irreducible] def sixthHighM22 : ℕ :=
    0

/-- The high odd-numerator mask of column `23`. -/
@[irreducible] def sixthHighM23 : ℕ :=
    0

/-- The high odd-numerator masks. -/
def sixthHighM : List ℕ :=
  [sixthHighM0, sixthHighM1, sixthHighM2, sixthHighM3, sixthHighM4, sixthHighM5, sixthHighM6,
    sixthHighM7, sixthHighM8, sixthHighM9, sixthHighM10, sixthHighM11, sixthHighM12,
    sixthHighM13, sixthHighM14, sixthHighM15, sixthHighM16, sixthHighM17, sixthHighM18,
    sixthHighM19, sixthHighM20, sixthHighM21, sixthHighM22, sixthHighM23]

/-- The positive spin phase mask. -/
@[irreducible] def sixthSpinP : ℕ :=
    0x20200000080800000000000000006868000000000000000000002929 |||
    (0x16800000000000000000000402900000000492000006108000000000000 <<< 256) |||
    (0x861000020490000000040290000000000000000000001680000 <<< 512) |||
    (0x2929000000000000000000006868000000000000000061610000494900000000 <<< 768) |||
    (0x1680000000000000000000000294000000000000000092040000108600000000 <<< 1024) |||
    (0x404000086860000000080800000000000000000000094940000 <<< 1280) |||
    (0x949400000000000000000000808000000000101000009292000000000000 <<< 1536) |||
    (0x86100000049200000000000000000294000000000000000000001680 <<< 1792) |||
    (0x4920000861000000000000000008016000000000000000000009402 <<< 2048) |||
    (0x808000000000000000000000949400000000040400008686000000000000 <<< 2304) |||
    (0x1010000092920000000094940000000000000000000080800000 <<< 2560) |||
    (0x9402000000000000000000008016000000000000000010860000920400000000 <<< 2816) |||
    (0x6868000000000000000000002929000000000000000020200000080800000000 <<< 3072) |||
    (0x2049000008610000000068010000000000000000000029400000 <<< 3328) |||
    (0x294000000000000000000000680100000000610800004920000000000000 <<< 3584) |||
    (0x61610000494900000000000000002929000000000000000000006868 <<< 3840)

/-- The negative spin phase mask. -/
@[irreducible] def sixthSpinN : ℕ :=
    0x49490000616100000000000000000101000000000000000000004040 |||
    (0x680100000000000000000000294000000000204900000861000000000000 <<< 256) |||
    (0x6108000049200000000029400000000000000000000068010000 <<< 512) |||
    (0x4040000000000000000000000101000000000000000008080000202000000000 <<< 768) |||
    (0x8016000000000000000000009402000000000000000004920000861000000000 <<< 1024) |||
    (0x9292000010100000000016160000000000000000000002020000 <<< 1280) |||
    (0x20200000000000000000000161600000000868600000404000000000000 <<< 1536) |||
    (0x10860000920400000000000000009402000000000000000000008016 <<< 1792) |||
    (0x92040000108600000000000000001680000000000000000000000294 <<< 2048) |||
    (0x161600000000000000000000020200000000929200001010000000000000 <<< 2304) |||
    (0x8686000004040000000002020000000000000000000016160000 <<< 2560) |||
    (0x294000000000000000000001680000000000000000086100000049200000000 <<< 2816) |||
    (0x101000000000000000000004040000000000000000049490000616100000000 <<< 3072) |||
    (0x4920000061080000000001680000000000000000000040290000 <<< 3328) |||
    (0x402900000000000000000000016800000000086100002049000000000000 <<< 3584) |||
    (0x8080000202000000000000000004040000000000000000000000101 <<< 3840)

/-- Row `0` of the eighth frame matrix. -/
def sixthFrameRow : List ℤ :=
  [-1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, -3, -3, 1, 5, 1, 1, 1, 1]

set_option maxRecDepth 100000 in
/-- The literal Golay table. -/
theorem sixthGolayTab_spec : ∀ d < 2048, fld 24 sixthGolayTab d = golayEncodedMask d := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal weight-class table. -/
theorem sixthWSignTab_spec : ∀ d < 2048,
    nortonUIntegerSign ((golayMaskWeight (golayEncodedMask d) / 4 : ℕ) : ZMod 2) =
      if sixthWSignTab.testBit d then -1 else 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal masks `sixthPosM`. -/
theorem sixthPosM_spec : ∀ j : Fin 24,
    generatedSixthMiddleOddPositiveMasks j = sixthPosM.getD j.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal masks `sixthNegM`. -/
theorem sixthNegM_spec : ∀ j : Fin 24,
    generatedSixthMiddleOddNegativeMasks j = sixthNegM.getD j.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal masks `sixthHighM`. -/
theorem sixthHighM_spec : ∀ j : Fin 24,
    generatedSixthMiddleOddHighMasks j = sixthHighM.getD j.val 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal positive spin mask. -/
theorem sixthSpinP_eq : generatedSixthSpinPositiveMask = sixthSpinP := by decide +kernel

set_option maxRecDepth 100000 in
/-- The literal negative spin mask. -/
theorem sixthSpinN_eq : generatedSixthSpinNegativeMask = sixthSpinN := by decide +kernel

set_option maxRecDepth 100000 in
/-- The literal frame row. -/
theorem sixthFrameRow_spec : ∀ j : Fin 24,
    generatedSixthFrameVectorData 8 0 j = sixthFrameRow.getD j.val 0 := by
  decide +kernel

/-! ## The fast numerator -/

/-- The tensor numerator `sixthTNum` evaluated from the literal tables. -/
def sixthTNumF (n j : ℕ) : ℤ :=
  8 * (if n.testBit 11 then -1 else 1) *
      (if (fld 24 sixthGolayTab (n % 2048)).testBit j then -1 else 1) *
      (((if (sixthPosM.getD j 0).testBit (n % 2048) then 1 else 0) -
        (if (sixthNegM.getD j 0).testBit (n % 2048) then 1 else 0)) *
        (if (sixthHighM.getD j 0).testBit (n % 2048) then 3 else 1)) -
    (if sixthWSignTab.testBit (n % 2048) then -1 else 1) *
      (if (fld 24 sixthGolayTab (n % 2048)).testBit j then -1 else 1) *
      sixthFrameRow.getD j 0 *
      (((if sixthSpinP.testBit (n % 2048) then 1 else 0) -
          (if sixthSpinN.testBit (n % 2048) then 1 else 0)) -
        ((if sixthSpinP.testBit (n % 2048 + 2048) then 1 else 0) -
          (if sixthSpinN.testBit (n % 2048 + 2048) then 1 else 0)))

/-- The fast numerator is the tensor numerator. -/
theorem sixthTNumF_eq (n : ℕ) (j : Fin 24) : sixthTNumF n j.val = sixthTNum n j := by
  have hd : n % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
  have h11 : nortonUIntegerSign (if n.testBit 11 then 1 else 0) =
      if n.testBit 11 then -1 else 1 := by
    cases n.testBit 11 <;> decide
  unfold sixthTNumF sixthTNum generatedSixthMiddleOddPackedNumerator generatedSixthPackedSpinPhase
  rw [sixthGolayTab_spec _ hd, sixthWSignTab_spec _ hd, sixthPosM_spec j, sixthNegM_spec j,
    sixthHighM_spec j, sixthFrameRow_spec j, sixthSpinP_eq, sixthSpinN_eq, h11]

/-! ## Compact columns -/

/-- The positive parts of column `0` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP0 : ℕ :=
    0x100010001010100010101010001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010100000101010100000001010100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 1280) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 2304) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010000000001010100000001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x100010001010001000000000100 <<< 3840) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x100010001010100010101010001 <<< 5376) |||
    (0x1010001000100000100010101010001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x9000101090100010000010001000101 <<< 6400) |||
    (0x1000101010100010000090001000901 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1000000000100010100010001000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10100000101000100000101000001 <<< 8448) |||
    (0x10100000101000100000101000001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 9984) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000001010000010001010000010100 <<< 11520) |||
    (0x1000001010000010100000101000001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 12544) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10100000101000100000101000001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000100010001000001000100010001 <<< 14080) |||
    (0x101010100000000010101010000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010101000000000000000001010101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1000101000100000100010900010000000000000000000000000000000000 <<< 15616) |||
    (0x101090100000000010101010000000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x100010001010100010101010001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010100000101010100000001010100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 17664) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 18688) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010000000001010100000001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x100010001010001000000000100 <<< 20224) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x100010001010100010101010001 <<< 21760) |||
    (0x1010001000100000100010101010001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x101000100010000010001000101 <<< 22784) |||
    (0x1000101010100010000000001000001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1000700000107010100010001000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10100000101000100000101000001 <<< 24832) |||
    (0x10100000101000100000101000001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 26368) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000001010000010001010000010100 <<< 27904) |||
    (0x1000001010000010100000101000001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 28928) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10100000101000100000101000001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1000100010001000001000100010001 <<< 30464) |||
    (0x101010100000000010101010007 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010101000700000000000001010101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1000101000100000100010000010000000000000000000000000000000000 <<< 32000) |||
    (0x101000100000000010101010000000000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `1` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP1 : ℕ :=
    0x1010001000100000001000000000100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010000000001010100000001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 1280) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 2304) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010100000101010100000001010100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010001000100000100010101010001 <<< 3840) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x100010001010100010101010001 <<< 5376) |||
    (0x1010001000100000100010101010001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000101010100010000010001000101 <<< 6400) |||
    (0x9000101090100010000010001000101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1000000000100010100010001000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10100000101000100000101000001 <<< 8448) |||
    (0x10100000101000100000101000001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 9984) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000001010000010001010000010100 <<< 11520) |||
    (0x1000001010000010100000101000001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x10107000101000001010000010100000000000000000000000000000000 <<< 12544) |||
    (0x100000101000001000101000000010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000001010000010001010000000100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x7010001000100010100010001000100 <<< 14080) |||
    (0x1010000000001010101000000000101 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10101010101010100000000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 15616) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010001000100000001000000000100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010000000001010100000001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 17664) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 18688) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010100000101010100000001010100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010001000100000100010101010001 <<< 20224) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x100010001010100010101010001 <<< 21760) |||
    (0x1010001000100000100010101010001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000101010100010007010001070101 <<< 22784) |||
    (0x101000100010000010001000101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x701000007000100010100010001000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10100000101000100000101000001 <<< 24832) |||
    (0x10100000101000100000101000001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 26368) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000001010000010001010000010100 <<< 27904) |||
    (0x1000001010000010100000101000001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 28928) |||
    (0x100000101000001000101000009010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000001010000010001010000090100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10001000100010100010001000100 <<< 30464) |||
    (0x1010000000001010101000000000101 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10101010101010100000000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 32000) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `2` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP2 : ℕ :=
    0x1010001000100000001000000000100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010000000001010100000001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 1280) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 2304) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010000000001010100000001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x100010001010001000000000100 <<< 3840) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010001000100000001000000000100 <<< 5376) |||
    (0x100010001010001000000000100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000101010100010000090001000901 <<< 6400) |||
    (0x1000101010100010000010001000101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1000000000100010100010001000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10100000101000100000101000001 <<< 8448) |||
    (0x10100000101000100000101000001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 9984) |||
    (0x1010000010100010000010107000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010101000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10100000101000100000101070001 <<< 11520) |||
    (0x10100000101000001000000010100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 12544) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10100000101000100000101000001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000100010001000001000100010001 <<< 14080) |||
    (0x1010000000001010101000000000101 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10101010101010100000000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 15616) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010001000100000001000000000100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010000000001010100000001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 17664) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 18688) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010000000001010100000001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x100010001010001000000000100 <<< 20224) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010001000100000001000000000100 <<< 21760) |||
    (0x100010001010001000000000100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000101010100010000000001000001 <<< 22784) |||
    (0x1000101010100010007010001070101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1000000000100010107010001070000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10100000101000100000101000001 <<< 24832) |||
    (0x10100000101000100000101000001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 26368) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010101090100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10100000101000100000101000001 <<< 27904) |||
    (0x10100000101000001090000010100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 28928) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10100000101000100000101000001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1000100010001000001000100010001 <<< 30464) |||
    (0x1010000000001010101000000000101 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10101010101010100000000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 32000) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `3` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP3 : ℕ :=
    0x100010001010100010101010001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010100000101010100000001010100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 1280) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 2304) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010100000101010100000001010100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010001000100000100010101010001 <<< 3840) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010001000100000001000000000100 <<< 5376) |||
    (0x100010001010001000000000100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000109010100090000010001000101 <<< 6400) |||
    (0x1000109010100090000010001000101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1000000000100010900010009000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000001010000010001010000000100 <<< 8448) |||
    (0x1000001010000010001010000000100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1000100010000000100010001000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x10000000101010100000101000000000000000000000000000000000000 <<< 9984) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000001010000010001010000010100 <<< 11520) |||
    (0x1000001010000010100000101000001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 12544) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10100000101000100000101000001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000100010001000001000100010001 <<< 14080) |||
    (0x1010000000001010101000000000101 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10101010101010100000000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 15616) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x100010001010100010101010001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010100000101010100000001010100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 17664) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 18688) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010100000101010100000001010100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010001000100000100010101010001 <<< 20224) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010001000100000001000000000100 <<< 21760) |||
    (0x100010001010001000000000100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000100010100000000010001000101 <<< 22784) |||
    (0x1000100010100000000010001000101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1000000000100010000010000000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000001010000010001010000090100 <<< 24832) |||
    (0x1000001010000010001010000090100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1000100010009000100010001000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x10900000101010100000101000000000000000000000000000000000000 <<< 26368) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000001010000010001010000010100 <<< 27904) |||
    (0x1000001010000010100000101000001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 28928) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10100000101000100000101000001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1000100010001000001000100010001 <<< 30464) |||
    (0x1010000000001010101000000000101 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10101010101010100000000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 32000) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `4` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP4 : ℕ :=
    0x1000101010100010101000100010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x100010101010009000001000000010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010000010000010001000901 <<< 3840) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010100010101000100010000 <<< 5376) |||
    (0x10000000001000101000100010007 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010001000000000100 <<< 6400) |||
    (0x100010001010001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010000000001010101 <<< 8448) |||
    (0x10101010000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000101010100000000 <<< 11520) |||
    (0x1010101000000000000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 12544) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010101000000000109 <<< 14080) |||
    (0x10001000100010100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010100000101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001000101000000010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010100010101000100010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x100010101010000000001000900010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010900010000010001000001 <<< 20224) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010100010101000100010000 <<< 21760) |||
    (0x10000070001000101000100010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010001000000000100 <<< 22784) |||
    (0x100010001010001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10101010000000001010101 <<< 24832) |||
    (0x10101010000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001010001000701000100000000000000000000000000000000 <<< 26368) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000000000101010100000000 <<< 27904) |||
    (0x1010101000700000000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 28928) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10101010000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010101000000000100 <<< 30464) |||
    (0x10001000100010100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001000101000009010000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `5` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP5 : ℕ :=
    0x10000000001000000010001000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x100010101010701000001000100010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100090000010000000101 <<< 3840) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010100010101000100010000 <<< 5376) |||
    (0x10000000001000101000107010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000100010101010001 <<< 6400) |||
    (0x1010001000100000100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010000000001010101 <<< 8448) |||
    (0x10101010000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000090100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010000000001010101 <<< 11520) |||
    (0x10101010101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 12544) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010901000000000101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000000010101010000 <<< 14080) |||
    (0x10001000100010100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010100000101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000701010000000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10000000001000000010001000101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x100010101010001000001000107010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100000000010009000101 <<< 20224) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010100010101000100010000 <<< 21760) |||
    (0x10000000001070101000100010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000100010101010001 <<< 22784) |||
    (0x1010001000100000100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10101010000000001010101 <<< 24832) |||
    (0x10101010000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000000100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 26368) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x700010101010000000001010101 <<< 27904) |||
    (0x10101010101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 28928) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010001000000000101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000000010101010000 <<< 30464) |||
    (0x10001000100010100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `6` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP6 : ℕ :=
    0x10000000001000000010001000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x100010101000001000001000100090100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010107010000010001000101 <<< 3840) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000000001000000010001000101 <<< 5376) |||
    (0x10000000701000101000100010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000100010101010001 <<< 6400) |||
    (0x100010001010001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010000000001010101 <<< 8448) |||
    (0x1010901000000000101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x9010001000001000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000101010100000000 <<< 11520) |||
    (0x10101010101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 12544) |||
    (0x101090100000000010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000000010101010000 <<< 14080) |||
    (0x10001000100010100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000001000000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10000000001000000010001000101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x100010101090001000001000100000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100010000010001070101 <<< 20224) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10000000001000000010001000101 <<< 21760) |||
    (0x10000000001000101000100010700 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000100010101010001 <<< 22784) |||
    (0x100010001010001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10101010000000001010101 <<< 24832) |||
    (0x1010001000000000101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 26368) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10001000001000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000000000101010100000000 <<< 27904) |||
    (0x10101010101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 28928) |||
    (0x101000100000000010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10101010000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000000010101010000 <<< 30464) |||
    (0x10001000100010100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000001090000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `7` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP7 : ℕ :=
    0x1000101010100010101000100010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x100010109010001000001000100010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101090100010000010001000100 <<< 3840) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000000001000000010001000101 <<< 5376) |||
    (0x10000000000000101000100090000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010001000000000100 <<< 6400) |||
    (0x1010001000100000100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010901000000000101010100000000 <<< 8448) |||
    (0x10101010000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 9984) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000101010100000000 <<< 11520) |||
    (0x10101010101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000000010101010000 <<< 14080) |||
    (0x100010001000001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010100000101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010100010101000100010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x100010100010001000001000100010900000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101000100010000010001000109 <<< 20224) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10000000001000000010001000101 <<< 21760) |||
    (0x10000000009000101000100000000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010001000000000100 <<< 22784) |||
    (0x1010001000100000100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010001000000000101010100000000 <<< 24832) |||
    (0x10101010000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 26368) |||
    (0x70001010101000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000000000101010100000000 <<< 27904) |||
    (0x10101010101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100010001070001000100000000000000000000000000000000 <<< 28928) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10101010000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000000010101010000 <<< 30464) |||
    (0x9000100010001000001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `8` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP8 : ℕ :=
    0x1000101010001010101010100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010001010001010001000001010001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100000101010009000001000100010100000000000000000000000000000000 <<< 1280) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101010001000009000100010000000000000000000000000000000000 <<< 2304) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x100000100000100010100000100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100000000000001 <<< 3840) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1000000070100010100010001000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010001010101010100 <<< 5376) |||
    (0x1010100010000000001010101010100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000000000000010101010001000000 <<< 6400) |||
    (0x1000000000000010101010001000000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000100000100010100010000010001 <<< 8448) |||
    (0x1000100000100010100010000010001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 9984) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10001010001000001000101000100 <<< 11520) |||
    (0x10001010001000100010000010001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1090101010101010000000000000000000000000000000000000000 <<< 12544) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000100000100010100010000010001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10100010000010001010001000001 <<< 14080) |||
    (0x1010101010101010000000000000000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x101000001010000010100000101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100000101000001000101000000010000000000000000000000000000000000 <<< 15616) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010001010101010100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010001010001010001000001010001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100090101010000000001000100010100000000000000000000000000000000 <<< 17664) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101010001000000000100010900000000000000000000000000000000 <<< 18688) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x100000100000100010100000100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100000000000001 <<< 20224) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x701000000000100010100010001000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010001010101010100 <<< 21760) |||
    (0x1010100010000000001010101010100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000000000000010101010001000000 <<< 22784) |||
    (0x1000000000000010101010001000000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000100000100010100010000010001 <<< 24832) |||
    (0x1000100000100010100010000010001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x70001010101000000000101010100000000000000000000000000000000 <<< 26368) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010000000001010101000700000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10001010001000001000101000100 <<< 27904) |||
    (0x10001010001000100010000010001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101010101010000000000000000000000000000000000000000 <<< 28928) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000100000100010100010000010001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10100010000010001010001000001 <<< 30464) |||
    (0x1010101010101010000000000000000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x101000001010000010100000101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100000101000001000101000009010000000000000000000000000000000000 <<< 32000) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `9` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP9 : ℕ :=
    0x1010100010000000100000000000001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010001010001010001000001010001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x900010101000001000001000100010100000000000000000000000000000000 <<< 1280) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x900010101000001000001000100010100000000000000000000000000000000 <<< 2304) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010001010001010001000001010001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100000000000001 <<< 3840) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1000000000100000100010009000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010001010101010100 <<< 5376) |||
    (0x1000101010100000000000001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000000000000010101010001000000 <<< 6400) |||
    (0x10101010101000000000100010101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10001010001000001000109000100 <<< 8448) |||
    (0x1000100000100010100010000010001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 9984) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000100000100010100010000010001 <<< 11520) |||
    (0x10001010001000100010000010001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12544) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000100000100010100010000010001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000001000101000100000100010100 <<< 14080) |||
    (0x1010101010101010000000000000000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010000000100000101000001010000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 15616) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010100010000000100000000000001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010001010001010001000001010001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x10101090001000001000100010100000000000000000000000000000000 <<< 17664) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x10101090001000001000100010100000000000000000000000000000000 <<< 18688) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010001010001010001000001010001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100000000000001 <<< 20224) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1000000000100090100010000000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010001010101010100 <<< 21760) |||
    (0x1000101010100000000000001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000000000000010101010001000000 <<< 22784) |||
    (0x10101010101000000000100010101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10001010001000001000100000100 <<< 24832) |||
    (0x1000100000100010100010000010001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 26368) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000100000100010100010007010001 <<< 27904) |||
    (0x10001010001000100010000010001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 28928) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000100000100010100010000010001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1070001000101000100000100010100 <<< 30464) |||
    (0x1010101010101010000000000000000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010000090100000101000001010000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32000) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `10` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP10 : ℕ :=
    0x1010100010000000100000000000001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x100000100000100010100000100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101010001070001000100010100000000000000000000000000000000 <<< 1280) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100000101010009000001000100010100000000000000000000000000000000 <<< 2304) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010001010001010001000001010001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010100010000000001010101010100 <<< 3840) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1070000000100010100010001000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010100010000000100000000000001 <<< 5376) |||
    (0x1000101010100000000000001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10101010101000000000100010101 <<< 6400) |||
    (0x10101010101000000000100010101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000100000100010100010000010001 <<< 8448) |||
    (0x1000100000100010100010000010001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100000100010900000101000100000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 9984) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10001010001000001000101000100 <<< 11520) |||
    (0x10001010001000100010000010001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12544) |||
    (0x1000101000100000100010900010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000100000100010100010000010001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10100010000010001010001000001 <<< 14080) |||
    (0x1010101010101010000000000000000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x101000001010000010100000101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 15616) |||
    (0x101000701010000000001010000010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010100010000000100000000000001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x100000100000100010100000100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101010001000001000107010100000000000000000000000000000000 <<< 17664) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100090101010000000001000100010100000000000000000000000000000000 <<< 18688) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010001010001010001000001010001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010100010000000001010101010100 <<< 20224) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1000000000107010100010001000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010100010000000100000000000001 <<< 21760) |||
    (0x1000101010100000000000001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10101010101000000000100010101 <<< 22784) |||
    (0x10101010101000000000100010101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000100000100010100010000010001 <<< 24832) |||
    (0x1000100000100010100010000010001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100000100010000000101000100000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 26368) |||
    (0x100010000010001010001000701000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10001010001000001000101000100 <<< 27904) |||
    (0x10001010001000100010000010001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 28928) |||
    (0x1000101000100000100010000010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000100000100010100010000010001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10100010000010001010001000001 <<< 30464) |||
    (0x1010101010101010000000000000000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x101000001010000010100000101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32000) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `11` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP11 : ℕ :=
    0x1000101010001010101010100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x100000100000100010100000100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101010001000009000100010000000000000000000000000000000000 <<< 1280) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101010001070001000100010100000000000000000000000000000000 <<< 2304) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x100000100000100010100000100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010100010000000001010101010100 <<< 3840) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1000000000100010100010001000700000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010100010000000100000000000001 <<< 5376) |||
    (0x1010100010000000001010101010100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10101010101000000000100010101 <<< 6400) |||
    (0x1000000000000010101010001000000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000100000100010100010000010001 <<< 8448) |||
    (0x10001010001000001000109000100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 9984) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10001010001000001000101000100 <<< 11520) |||
    (0x1000100000100010001000901000100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12544) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10001010001000001000109000100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10100010000010001010001000001 <<< 14080) |||
    (0x101010101010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x101000001010000010100000101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 15616) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010001010101010100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x100000100000100010100000100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101010001000000000100010900000000000000000000000000000000 <<< 17664) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101010001000001000107010100000000000000000000000000000000 <<< 18688) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x100000100000100010100000100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010100010000000001010101010100 <<< 20224) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1000000000100010107010001000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010100010000000100000000000001 <<< 21760) |||
    (0x1010100010000000001010101010100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10101010101000000000100010101 <<< 22784) |||
    (0x1000000000000010101010001000000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000100000100010100010000010001 <<< 24832) |||
    (0x10001010001000001000100000100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 26368) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10001010001000001000101000100 <<< 27904) |||
    (0x1000100000100010001000001000100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 28928) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10001010001000001000100000100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10100010000010001010001000001 <<< 30464) |||
    (0x101010101010901 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x101000001010000010100000101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32000) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `12` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP12 : ℕ :=
    0x1000000010101000101010000010101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10000000701000101000100010000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 1280) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 2304) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000101010100010000090000000101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000000010101000000000101000000 <<< 3840) |||
    (0x1070000000100010100010001000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000000010101000101010000010101 <<< 5376) |||
    (0x10101000000010101010000010101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010000000001010100000001 <<< 6400) |||
    (0x1010000000001010100000001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x101010100000000010101010000 <<< 8448) |||
    (0x101010100000000010101010000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 9984) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010000000001010101000000000101 <<< 11520) |||
    (0x1010000000001010000010101010000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 12544) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x101010100000000010101010000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010901000000000101010100000000 <<< 14080) |||
    (0x10100000101000100000101070001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000100010001000100010001000100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10101010101010100000000000000000000000000000000 <<< 15616) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000000010101000101010000010101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10007000001000101000100010000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 17664) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 18688) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000101010100010000000009000101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000000010101000000000101000000 <<< 20224) |||
    (0x1000007000100010100010001000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000000010101000101010000010101 <<< 21760) |||
    (0x10101000000010101010000010101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010000000001010100000001 <<< 22784) |||
    (0x1010000000001010100000001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x101010100000000010101010000 <<< 24832) |||
    (0x101010100000000010101010000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101010100070000000000000101010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 26368) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100010000010001010001000701000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010000000001010101000000000101 <<< 27904) |||
    (0x1010000000001010000010101010000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 28928) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x101010100000000010101010000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010001000000000101010100000000 <<< 30464) |||
    (0x10100000101000100000101000001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000100010001000100010001000100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10101010101010100000000000000000000000000000000 <<< 32000) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `13` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP13 : ℕ :=
    0x10101000000010000000101000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10000000001000101000107010000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 1280) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 2304) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000101010100010000010701000101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10101000000010101010000010101 <<< 3840) |||
    (0x1000000000100010100010701000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000000010101000101010000010101 <<< 5376) |||
    (0x1000000010101000000000101000000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010100000101010100000001010100 <<< 6400) |||
    (0x1010000000001010100000001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010000000001010101000000000109 <<< 8448) |||
    (0x101010100000000010101010000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 9984) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010000000001010101000000000101 <<< 11520) |||
    (0x101010100000901000000000101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 12544) |||
    (0x101000000000101010100000000010900000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x101010100000000010101010000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10101010000000001010101 <<< 14080) |||
    (0x1000001010000010001010000010100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000100010001000100010001000100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101010101010101000000000000070000000000000000000000000000000000 <<< 15616) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10101000000010000000101000000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10000000001000101070100010000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 17664) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 18688) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000101010100010000010001070101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10101000000010101010000010101 <<< 20224) |||
    (0x1000000000100010107010001000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000000010101000101010000010101 <<< 21760) |||
    (0x1000000010101000000000101000000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010100000101010100000001010100 <<< 22784) |||
    (0x1010000000001010100000001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010000000001010101000000000100 <<< 24832) |||
    (0x101010100000000010101010000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 26368) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010000000001010101000000000101 <<< 27904) |||
    (0x101010100000001000000000101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 28928) |||
    (0x101000000000101010100000000010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x101010100000000010101010000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10101010000000001010101 <<< 30464) |||
    (0x1000001010000010001010000010100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000100010001000100010001000100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 32000) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `14` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP14 : ℕ :=
    0x10101000000010000000101000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10700000001000101000100010000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 1280) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 2304) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000001090100010000010001000101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10101000000010101010000010101 <<< 3840) |||
    (0x1000000000100010100000009000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10101000000010000000101000000 <<< 5376) |||
    (0x10101000000010101010000010101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010000000001010100000001 <<< 6400) |||
    (0x1010100000101010100000001010100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x101010100000000010101010000 <<< 8448) |||
    (0x1010000000001010101000000000109 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 9984) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x101010100000000010101010000 <<< 11520) |||
    (0x1010000000001010000010101010000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 12544) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x101010100000000010101010000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10101010000000001010101 <<< 14080) |||
    (0x1000001010000010001010000010100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000100010001000100010001000100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10101010101010100000000000000000000000000000000 <<< 15616) |||
    (0x701000100010001010001000100010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10101000000010000000101000000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10000070001000101000100010000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 17664) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 18688) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000901000100010000010001000101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10101000000010101010000010101 <<< 20224) |||
    (0x1000000000100010100090000000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10101000000010000000101000000 <<< 21760) |||
    (0x10101000000010101010000010101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010000000001010100000001 <<< 22784) |||
    (0x1010100000101010100000001010100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x101010100000000010101010000 <<< 24832) |||
    (0x1010000000001010101000000000100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 26368) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x101010100000000010101010007 <<< 27904) |||
    (0x1010000000001010000010101010000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010001000701010000010001010000000000000000000000000000000000 <<< 28928) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x101010100000000010101010000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10101010000000001010101 <<< 30464) |||
    (0x1000001010000010001010000010100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000100010001000100010001000100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10101010101010100000000000000000000000000000000 <<< 32000) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `15` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP15 : ℕ :=
    0x1000000010101000101010000010101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10000000001000101000000090000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 1280) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 2304) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000109010000010000010001000101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000000010101000000000101000000 <<< 3840) |||
    (0x1000000070100010100010001000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10101000000010000000101000000 <<< 5376) |||
    (0x1000000010101000000000101000000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010100000101010100000001010100 <<< 6400) |||
    (0x1010100000101010100000001010100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x101010100000000010101010000 <<< 8448) |||
    (0x101010100000000010101010000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x9010001000001000101000100000100000000000000000000000000000000 <<< 9984) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010000000001010101000000000101 <<< 11520) |||
    (0x1010000000001010000010101010000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 12544) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010000000001010101000000000109 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10101010000000001010101 <<< 14080) |||
    (0x1000001010000010001010000010100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10001000100000001000100010001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10101010101010100000000000000000000000000000000 <<< 15616) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000000010101000101010000010101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10000000001000101000900000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 17664) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 18688) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000100010900010000010001000101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000000010101000000000101000000 <<< 20224) |||
    (0x1000700000100010100010001000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10101000000010000000101000000 <<< 21760) |||
    (0x1000000010101000000000101000000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010100000101010100000001010100 <<< 22784) |||
    (0x1010100000101010100000001010100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x101010100000000010101010000 <<< 24832) |||
    (0x101010100000000010101010000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x10001000001000101000100000100000000000000000000000000000000 <<< 26368) |||
    (0x10101010000000001010101000700000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010000000001010101000000000101 <<< 27904) |||
    (0x1010000000001010000010101010000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 28928) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010000000001010101000000000100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10101010000000001010101 <<< 30464) |||
    (0x1000001010000010001010000010100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10001000100090001000100010001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10101010101010100000000000000000000000000000000 <<< 32000) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `16` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP16 : ℕ :=
    0x3000303000003000303000303000303 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x30303030303000303030003000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 1280) |||
    (0x300030300000300000003000003000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 2304) |||
    (0x3000003030003000003000003000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x3000000000000030000000300030303 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x3000303000003000000030000030000 <<< 3840) |||
    (0x3030303030300030303000300000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x3000303000003000303000303000303 <<< 5376) |||
    (0x30000030300030303000303000303 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x300000300000003000003030003 <<< 6400) |||
    (0x300000300000003000003030003 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x303000303000303030003030000030000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x300030303030003000503000300030300000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x0 <<< 8448) |||
    (0x0 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x303000003030000000003030000030300000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x300030003000300030003000300030000000000000000000000000000000000 <<< 9984) |||
    (0x303030303030303030b03030303030300000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x300000303000003030000030300000300000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x303030303030303030b030303030303 <<< 11520) |||
    (0x3030303030303030000000000000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0xb00030003000300000300030003000300000000000000000000000000000000 <<< 12544) |||
    (0x0 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x0 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x30300000b0300000303000003030000 <<< 14080) |||
    (0x30003030003000300030500030003 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x3050003000303000300000300030300 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x30303030000000300000000030300000000000000000000000000000000 <<< 15616) |||
    (0x300000300030000000303000300000300000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x3000303000003000303000303000303 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x30303030303000303030003000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 17664) |||
    (0x300030300000300000003000003000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 18688) |||
    (0x3000003030003000003000003000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x3000000000000030000000300030303 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x3000303000003000000030000030000 <<< 20224) |||
    (0x3030303030300030303000300000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x3000303000003000303000303000303 <<< 21760) |||
    (0x30000030300030303000303000303 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x300000300000003000003030003 <<< 22784) |||
    (0x300000300000003000003030003 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x303000303000303030003030000030000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x305030303030503050003050315030300000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x5000000000000 <<< 24832) |||
    (0x5000000000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x303000503030000000003030000030300000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x300030003000305030003000300030000000000000000000000000000000000 <<< 26368) |||
    (0x303030303030303030003030303030300000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x300000303000003030005030300000300000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x3030303030303030300030303030303 <<< 27904) |||
    (0x3030303030303030000000000000500 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x30003000300000300030003000300000000000000000000000000000000 <<< 28928) |||
    (0x500000000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x5000000000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x3030000000300000303000003030000 <<< 30464) |||
    (0x30003030003000300030000030003 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x3000003000303000300000300030300 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x303030300000b0300000000030300000000000000000000000000000000 <<< 32000) |||
    (0x300000300030b00000303000300000300000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `17` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP17 : ℕ :=
    0x3000303000003000303000303000303 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x30303030303000303030003000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 1280) |||
    (0x300030300000300000003000003000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 2304) |||
    (0x3000003030003000003000003000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x3000000000000030000000300030303 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x3000303000003000000030000030000 <<< 3840) |||
    (0x3030303030300030303000300000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x3000303000003000303000303000303 <<< 5376) |||
    (0x30000030300030303000303000303 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x300000300000003000003030003 <<< 6400) |||
    (0x300000300000003000003030003 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x303000303000303030003030000030000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x300030303030003000503000300030300000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x0 <<< 8448) |||
    (0x0 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x303000003030000000003030000030300000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x300030003000300030003000300030000000000000000000000000000000000 <<< 9984) |||
    (0x303030303030303030b03030303030300000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x300000303000003030000030300000300000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x303030303030303030b030303030303 <<< 11520) |||
    (0x3030303030303030000000000000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0xb00030003000300000300030003000300000000000000000000000000000000 <<< 12544) |||
    (0x0 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x0 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x30300000b0300000303000003030000 <<< 14080) |||
    (0x30003030003000300030500030003 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x3050003000303000300000300030300 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x30303030000000300000000030300000000000000000000000000000000 <<< 15616) |||
    (0x300000300030000000303000300000300000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x3000303000003000303000303000303 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x30303030303000303030003000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 17664) |||
    (0x300030300000300000003000003000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 18688) |||
    (0x3000003030003000003000003000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x3000000000000030000000300030303 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x3000303000003000000030000030000 <<< 20224) |||
    (0x3030303030300030303000300000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x3000303000003000303000303000303 <<< 21760) |||
    (0x30000030300030303000303000303 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x300000300000003000003030003 <<< 22784) |||
    (0x300000300000003000003030003 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x303000303000303030003030000030000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x305030303030503050003050315030300000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x5000000000000 <<< 24832) |||
    (0x5000000000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x303000503030000000003030000030300000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x300030003000305030003000300030000000000000000000000000000000000 <<< 26368) |||
    (0x303030303030303030003030303030300000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x300000303000003030005030300000300000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x3030303030303030300030303030303 <<< 27904) |||
    (0x3030303030303030000000000000500 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x30003000300000300030003000300000000000000000000000000000000 <<< 28928) |||
    (0x500000000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x5000000000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x3030000000300000303000003030000 <<< 30464) |||
    (0x30003030003000300030000030003 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x3000003000303000300000300030300 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x303030300000b0300000000030300000000000000000000000000000000 <<< 32000) |||
    (0x300000300030b00000303000300000300000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `18` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP18 : ℕ :=
    0x10000010100010000010000010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000000000010000000100010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 1280) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 2304) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101010101000101010001000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000010100010101000101000101 <<< 3840) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000010100010000010000010000 <<< 5376) |||
    (0x1000101000001000000010000010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001010001010100010100000100 <<< 6400) |||
    (0x1010001010001010100010100000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1070000070100010100010701000700000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x0 <<< 8448) |||
    (0x0 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 9984) |||
    (0x101010101010101010101010101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101010101010101010101010101 <<< 11520) |||
    (0x1010101010101010000000000000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 12544) |||
    (0x0 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x0 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000010100000101000001010000 <<< 14080) |||
    (0x10001010001000100010000010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001000101000100000100010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 15616) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10000010100010000010000010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000000000010000000100010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 17664) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 18688) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101010101000101010001000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000010100010101000101000101 <<< 20224) |||
    (0x100000000000001000000010001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10000010100010000010000010000 <<< 21760) |||
    (0x1000101000001000000010000010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001010001010100010100000100 <<< 22784) |||
    (0x1010001010001010100010100000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10000010000000100000101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x701000707000107010107010001070000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x0 <<< 24832) |||
    (0x0 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 26368) |||
    (0x101010101010101010101010101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101010101010101010101010101 <<< 27904) |||
    (0x1010101010101010000000000000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010001000100000100010001000100000000000000000000000000000000 <<< 28928) |||
    (0x0 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x0 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000010100000101000001010000 <<< 30464) |||
    (0x10001010001000100010000010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001000101000100000100010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 32000) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `19` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP19 : ℕ :=
    0x50000050500050000050000050000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x5000000000000050000000500050505 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x505050000050505000505050000000500000000000000000000000000000000 <<< 1280) |||
    (0x5000005050005050500050500050500000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x505050000050505000505050000000500000000000000000000000000000000 <<< 2304) |||
    (0x500050500000500050500050500050500000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x50505050505000505050005000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x50000050500050505000505000505 <<< 3840) |||
    (0x500000000000005000000050005050500000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x505000000050000000505050000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x50000050500050000050000050000 <<< 5376) |||
    (0x5000505000005000000050000050000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x5050005050005050500050500000500 <<< 6400) |||
    (0x5050005050005050500050500000500 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x50000050000000500000505000500000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1d000000001d001d00001d000d000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x505050505050505051d050505050505 <<< 8448) |||
    (0x505050505050505051d050505050505 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x51d00000505050500000505000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x500050005001d000500050005000500000000000000000000000000000000 <<< 9984) |||
    (0x0 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x505000005050000051d000005050000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x0 <<< 11520) |||
    (0x505050505051d05 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x5000500050005050005000500050000000000000000000000000000000000 <<< 12544) |||
    (0x505050505050505051d05050505050500000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x505050505050505051d050505050505 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x505000005050000050500000505 <<< 14080) |||
    (0x5000500000500050005000005000500 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x500050000050005050005000005 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x505000000000505130005050505000000000000000000000000000000000000 <<< 15616) |||
    (0x5050005001305050000050005050000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x50000050500050000050000050000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x5000000000000050000000500050505 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x505050000050505000505050000000500000000000000000000000000000000 <<< 17664) |||
    (0x5000005050005050500050500050500000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x505050000050505000505050000000500000000000000000000000000000000 <<< 18688) |||
    (0x500050500000500050500050500050500000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x50505050505000505050005000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x50000050500050505000505000505 <<< 20224) |||
    (0x500000000000005000000050005050500000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x505000000050000000505050000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x50000050500050000050000050000 <<< 21760) |||
    (0x5000505000005000000050000050000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x5050005050005050500050500000500 <<< 22784) |||
    (0x5050005050005050500050500000500 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x50000050000000500000505000500000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1d00000000000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x5050505050505050500050505050505 <<< 24832) |||
    (0x5050505050505050500050505050505 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x50000000505050500000505000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x5000500050000000500050005000500000000000000000000000000000000 <<< 26368) |||
    (0x1300000000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x5050000050500000500000005050000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x13000000000000 <<< 27904) |||
    (0x505050505050005 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1305000500050005050005000500050000000000000000000000000000000000 <<< 28928) |||
    (0x505050505050505050005050505050500000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x5050505050505050500050505050505 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x505130005050000050500000505 <<< 30464) |||
    (0x5000500000500050005001d05000500 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1d0500050000050005050005000005 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x505000000000505000005050505000000000000000000000000000000000000 <<< 32000) |||
    (0x5050005000005050000050005050000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `20` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP20 : ℕ :=
    0x10000000001000101000100010007 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x100000101010001000001000100090100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000001000000010001000101 <<< 3840) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000000001000101000107010000 <<< 5376) |||
    (0x1000101010100010101000100010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000001000000000100 <<< 6400) |||
    (0x1010001000100000001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000000000001010101 <<< 8448) |||
    (0x1010101000000000000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010101010100000000 <<< 11520) |||
    (0x10101010000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100000100010900010000000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000101000000000101 <<< 14080) |||
    (0x1000100010001000100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000100000101070001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10007000001000101000100010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x100090101010001000001000100000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000001000000010001000101 <<< 20224) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x7010000000001000101000100010000 <<< 21760) |||
    (0x1000101010100010101000100010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000001000000000100 <<< 22784) |||
    (0x1010001000100000001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000000000000000001010101 <<< 24832) |||
    (0x1010101000000000000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000000001010101000700000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 26368) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10101010101010100000000 <<< 27904) |||
    (0x700010101010000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100000100010000010000000000000000000000000000000000 <<< 28928) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000000000000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000101000000000101 <<< 30464) |||
    (0x1000100010001000100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `21` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP21 : ℕ :=
    0x1000101000100090000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x100010901010001000001000100010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100010101000100010000 <<< 3840) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000000001000101000100010007 <<< 5376) |||
    (0x1000101010100010101000100010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010100010101010001 <<< 6400) |||
    (0x100010001010100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000000000001010101 <<< 8448) |||
    (0x1010101000000000000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001000100090100010000000000000000000000000000000000 <<< 9984) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000000000001010101 <<< 11520) |||
    (0x1010101000000000101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x1090101010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000101000000000101 <<< 14080) |||
    (0x10001000100000001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010001010000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x90000000001000101000100000000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x100010001010001000001000100010900000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100010101000100010000 <<< 20224) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10007000001000101000100010000 <<< 21760) |||
    (0x1000101010100010101000100010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010100010101010001 <<< 22784) |||
    (0x100010001010100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000000000000000001010101 <<< 24832) |||
    (0x1010101000000000000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001000100000100010000000000000000000000000000000000 <<< 26368) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000700000000000001010101 <<< 27904) |||
    (0x1010101000000000101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 28928) |||
    (0x1000101010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000000000000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000101000000000101 <<< 30464) |||
    (0x10001000100090001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010001010000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `22` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP22 : ℕ :=
    0x10700000001000101000100010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x107010101010001000001000100010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000001000000010001000101 <<< 3840) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10700000001000101000100010000 <<< 5376) |||
    (0x10000000001000000010001000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010100010101010001 <<< 6400) |||
    (0x1010001000100000001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10901010101010100000000 <<< 8448) |||
    (0x1010101000000000000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010900000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010101010100000000 <<< 11520) |||
    (0x1010101000000000101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10901010101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000101000000000101 <<< 14080) |||
    (0x1000100010001000100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010001010000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001010007010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10000000001000101000100010700 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x100010101010001000001000107010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000001000000010001000101 <<< 20224) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10000000001000101000100010700 <<< 21760) |||
    (0x10000000001000000010001000101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010100010101010001 <<< 22784) |||
    (0x1010001000100000001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10001010101010100000000 <<< 24832) |||
    (0x1010101000000000000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 26368) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010000000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10101010101010100000000 <<< 27904) |||
    (0x1010101000000000101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 28928) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10001010101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000101000000000101 <<< 30464) |||
    (0x1000100010001000100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010001010000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 32256)

/-- The positive parts of column `23` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXP23 : ℕ :=
    0x10000000001000101000107010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x900010101010001000001000000010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100010101000100010000 <<< 3840) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101000100090000 <<< 5376) |||
    (0x10000000001000000010001000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000001000000000100 <<< 6400) |||
    (0x100010001010100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000000000001010101 <<< 8448) |||
    (0x10901010101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010101010100000000 <<< 11520) |||
    (0x1010101000000000101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010000010101010000 <<< 14080) |||
    (0x1000100010001000100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010001010000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10107000101000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x7010000000001000101000100010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x10101010001000001000900010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100010101000100010000 <<< 20224) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x90000000001000101000100000000 <<< 21760) |||
    (0x10000000001000000010001000101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000001000000000100 <<< 22784) |||
    (0x100010001010100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000000000000000001010101 <<< 24832) |||
    (0x10001010101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 26368) |||
    (0x101010100070000000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10101010101010100000000 <<< 27904) |||
    (0x1010101000000000101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 28928) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000000000000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010700010101010000 <<< 30464) |||
    (0x1000100010001000100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010001010000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 32256)

/-- The positive parts of the columns. -/
def sixthSXP : List ℕ :=
  [sixthSXP0, sixthSXP1, sixthSXP2, sixthSXP3, sixthSXP4, sixthSXP5, sixthSXP6, sixthSXP7,
    sixthSXP8, sixthSXP9, sixthSXP10, sixthSXP11, sixthSXP12, sixthSXP13, sixthSXP14, sixthSXP15,
    sixthSXP16, sixthSXP17, sixthSXP18, sixthSXP19, sixthSXP20, sixthSXP21, sixthSXP22,
    sixthSXP23]

/-- The negative parts of column `0` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN0 : ℕ :=
    0x1010001000100000001000000000100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010000000001010100000001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 1280) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 2304) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010100000101010100000001010100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010001000100000100010101010001 <<< 3840) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010001000100000001000000000100 <<< 5376) |||
    (0x100010001010001000000000100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10000000001000101000100010000 <<< 6400) |||
    (0x10000000001000101000100010000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100010901010009000001000100010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000001010000010001010000010100 <<< 8448) |||
    (0x1000001010000010001010000010100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 9984) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010101010100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10100000101000100000101000001 <<< 11520) |||
    (0x10100000101000001010000010100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 12544) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000001010000010001010000010100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10001000100010100010001000100 <<< 14080) |||
    (0x1010000000001010101000000000109 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10901010101010100000000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 15616) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010001000100000001000000000100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010000000001010100000001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 17664) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 18688) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010100000101010100000001010100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010001000100000100010101010001 <<< 20224) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010001000100000001000000000100 <<< 21760) |||
    (0x100010001010001000000000100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x7010000070001000101000100010000 <<< 22784) |||
    (0x10000000001000101070100010700 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100010001010000000001000100010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000001010000010001010000010100 <<< 24832) |||
    (0x1000001010000010001010000010100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 26368) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010101010100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10100000101000100000101000001 <<< 27904) |||
    (0x10100000101000001010000010100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 28928) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000001010000010001010000010100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10001000100010100010001000100 <<< 30464) |||
    (0x1010000000001010101000000000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10001010101010100000000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100010000010001010001000701000100000000000000000000000000000000 <<< 32000) |||
    (0x70001010101000000000101010100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `1` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN1 : ℕ :=
    0x100010001010100010101010001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010100000101010100000001010100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 1280) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 2304) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010000000001010100000001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x100010001010001000000000100 <<< 3840) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010001000100000001000000000100 <<< 5376) |||
    (0x100010001010001000000000100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10000000001000109000100090000 <<< 6400) |||
    (0x10000000001000101000100010000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x900010109010001000001000100010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000001010000010001010000010100 <<< 8448) |||
    (0x1000001010000010001010000010100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 9984) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010101010100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10100000101000100000101000001 <<< 11520) |||
    (0x10100000101000001010000010100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101000000010000010100000101000000000000000000000000000000000000 <<< 12544) |||
    (0x1010000010100010000010107000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10100000101000100000101070001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x100010001000001000100010001 <<< 14080) |||
    (0x101010100000000010101010000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010101000000000000000001010101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 15616) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x100010001010100010101010001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010100000101010100000001010100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 17664) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 18688) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010000000001010100000001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x100010001010001000000000100 <<< 20224) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010001000100000001000000000100 <<< 21760) |||
    (0x100010001010001000000000100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10000000001000100000100000000 <<< 22784) |||
    (0x7010000070001000101000100010000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10100010001000001000100010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000001010000010001010000010100 <<< 24832) |||
    (0x1000001010000010001010000010100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 26368) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010101010100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10100000101000100000101000001 <<< 27904) |||
    (0x10100000101000001010000010100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101000009010000010100000101000000000000000000000000000000000000 <<< 28928) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10100000101000100000101000001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x9000100010001000001000100010001 <<< 30464) |||
    (0x101010100000000010101010000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010101000000000000000001010101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 32000) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `2` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN2 : ℕ :=
    0x100010001010100010101010001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010100000101010100000001010100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 1280) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 2304) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010100000101010100000001010100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010001000100000100010101010001 <<< 3840) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x100010001010100010101010001 <<< 5376) |||
    (0x1010001000100000100010101010001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10000000001000101000100010000 <<< 6400) |||
    (0x10000000001000109000100090000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100010101010001000009000100090100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000001010000010001010000010100 <<< 8448) |||
    (0x1000001010000010001010000010100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 9984) |||
    (0x100000101000001000101000000010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101010101010101000000000000070000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000001010000010001010000000100 <<< 11520) |||
    (0x1000001010000010100070101000001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 12544) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000001010000010001010000010100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10001000100010100010001000100 <<< 14080) |||
    (0x101010100000000010101010000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010101000000000000000001010101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 15616) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x100010001010100010101010001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010100000101010100000001010100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 17664) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 18688) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010100000101010100000001010100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010001000100000100010101010001 <<< 20224) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x100010001010100010101010001 <<< 21760) |||
    (0x1010001000100000100010101010001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10000000001000101070100010700 <<< 22784) |||
    (0x10000000001000100000100000000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100010101010001000000000100000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000001010000010001010000010100 <<< 24832) |||
    (0x1000001010000010001010000010100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 26368) |||
    (0x100000101000001000101000009010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000001010000010001010000090100 <<< 27904) |||
    (0x1000001010000010100000101000001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 28928) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000001010000010001010000010100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10001000100010100010001000100 <<< 30464) |||
    (0x101010100000000010101010000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010101000000000000000001010101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 32000) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `3` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN3 : ℕ :=
    0x1010001000100000001000000000100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010000000001010100000001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 1280) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 2304) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010000000001010100000001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x100010001010001000000000100 <<< 3840) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x100010001010100010101010001 <<< 5376) |||
    (0x1010001000100000100010101010001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10000000001000101000100010000 <<< 6400) |||
    (0x10000000001000101000100010000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100010101010001000001000100010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10100000101000100000101070001 <<< 8448) |||
    (0x10100000101000100000101070001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100010001000107010001000100010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101000701010000000001010000010100000000000000000000000000000000 <<< 9984) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010101010100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10100000101000100000101000001 <<< 11520) |||
    (0x10100000101000001010000010100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 12544) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000001010000010001010000010100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10001000100010100010001000100 <<< 14080) |||
    (0x101010100000000010101010000 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010101000000000000000001010101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 15616) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010001000100000001000000000100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010000000001010100000001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 17664) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 18688) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010000000001010100000001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x100010001010001000000000100 <<< 20224) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x100010001010100010101010001 <<< 21760) |||
    (0x1010001000100000100010101010001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10007000001070101000100010000 <<< 22784) |||
    (0x10007000001070101000100010000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100010101010001000701000107010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10100000101000100000101000001 <<< 24832) |||
    (0x10100000101000100000101000001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100010001000100010001000100010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 26368) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010101010100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10100000101000100000101000001 <<< 27904) |||
    (0x10100000101000001010000010100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 28928) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000001010000010001010000010100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x10001000100010100010001000100 <<< 30464) |||
    (0x101010100000000010101010000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010101000000000000000001010101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 32000) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `4` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN4 : ℕ :=
    0x10000000001000000010001000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x1000000000100010100010701000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000701000101000100010000 <<< 3840) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000000001000000010001000101 <<< 5376) |||
    (0x1000101090100010000010001000100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000100010101010001 <<< 6400) |||
    (0x1010001000100000100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000101010100000000 <<< 8448) |||
    (0x1010101000000000101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100000100010900010000000000000000000000000000000000 <<< 9984) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010000000001010101 <<< 11520) |||
    (0x10901010101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000000010101010000 <<< 14080) |||
    (0x1000100010001000001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000001010000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100010000010107000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10000000001000000010001000101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x1000000000107010100010001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000001000101000100010700 <<< 20224) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10000000001000000010001000101 <<< 21760) |||
    (0x1000101000100010000010001000109 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000100010101010001 <<< 22784) |||
    (0x1010001000100000100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000000000101010100000000 <<< 24832) |||
    (0x1010101000000000101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100000100010000010000000000000000000000000000000000 <<< 26368) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10101010000000001010101 <<< 27904) |||
    (0x10001010101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 28928) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000000000101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000000010101010007 <<< 30464) |||
    (0x1000100010001000001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000001010000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `5` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN5 : ℕ :=
    0x1000101010100010101000100010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x1000000000000010100010009000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000001000101000107010000 <<< 3840) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10000000001000000010001000101 <<< 5376) |||
    (0x1000101010100090000010000000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010001000000000100 <<< 6400) |||
    (0x100010001010001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000101010100000000 <<< 8448) |||
    (0x1010101000000000101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010901000000000101010100000000 <<< 11520) |||
    (0x1010101000000000000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010101000000000101 <<< 14080) |||
    (0x1000100010001000001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000001010000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10000000101010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010100010101000100010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x1000000000900010100010000000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000001070101000100010000 <<< 20224) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10000000001000000010001000101 <<< 21760) |||
    (0x1000101010100000000010009000101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010001000000000100 <<< 22784) |||
    (0x100010001010001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000000000101010100000000 <<< 24832) |||
    (0x1010101000000000101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101070001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 26368) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010001000000000101010100000000 <<< 27904) |||
    (0x1010101000000000000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 28928) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x700010101010000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010101000000000101 <<< 30464) |||
    (0x1000100010001000001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000001010000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10900000101010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `6` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN6 : ℕ :=
    0x1000101010100010101000100010000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x1000000070100010100010001000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000000000101000100090000 <<< 3840) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010100010101000100010000 <<< 5376) |||
    (0x1000101010000010000010001000901 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010001000000000100 <<< 6400) |||
    (0x1010001000100000100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000101010100000000 <<< 8448) |||
    (0x10101010000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010000000001010101 <<< 11520) |||
    (0x1010101000000000000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010101000000000101 <<< 14080) |||
    (0x1000100010001000001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010100070101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010100010101000100010000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x1000000000100010100010001070000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000009000101000100000000 <<< 20224) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010100010101000100010000 <<< 21760) |||
    (0x1000101010900010000010001000001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010001000000000100 <<< 22784) |||
    (0x1010001000100000100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000000000101010100000000 <<< 24832) |||
    (0x700010101010000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 26368) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x107000100010100010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10101010000000001010101 <<< 27904) |||
    (0x1010101000000000000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 28928) |||
    (0x70001010101000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000000000101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010101000000000101 <<< 30464) |||
    (0x1000100010001000001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `7` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN7 : ℕ :=
    0x10000000001000000010001000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x1000000000100010100010001000700000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000001000101000100010007 <<< 3840) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010100010101000100010000 <<< 5376) |||
    (0x1000101010107010000010001000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000100010101010001 <<< 6400) |||
    (0x100010001010001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010000000001010101 <<< 8448) |||
    (0x1010101000000000101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x101090100000000010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10101010000000001010101 <<< 11520) |||
    (0x1010101000000000000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001000100090100010000000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010101000000000101 <<< 14080) |||
    (0x7010001000100010100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000001010000010100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10000000001000000010001000101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x1000007000100010100010001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000070001000101000100010000 <<< 20224) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010100010101000100010000 <<< 21760) |||
    (0x1000101010100010000010001070101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000100010101010001 <<< 22784) |||
    (0x100010001010001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1000001010001010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x700010101010000000001010101 <<< 24832) |||
    (0x1010101000000000101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000010100000000010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 26368) |||
    (0x101000100000000010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10101010000000001010101 <<< 27904) |||
    (0x1010101000000000000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001000100000100010000000000000000000000000000000000 <<< 28928) |||
    (0x101010100000000010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000000000101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010101000000000101 <<< 30464) |||
    (0x10001000100010100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000001010000010100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `8` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN8 : ℕ :=
    0x1010100010000000100000000000001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x100000100000100010100000100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1070000000100010100010001000000000000000000000000000000000000 <<< 1280) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1000000000100010100010001000700000000000000000000000000000000 <<< 2304) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010001010001010001000001010001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010100010000000001010101010100 <<< 3840) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x900010101000001000001000100010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010100010000000100000000000001 <<< 5376) |||
    (0x1000101010100000000000001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10101010101000000000100010101 <<< 6400) |||
    (0x10101010101000000000100010101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10001010001000001000101000100 <<< 8448) |||
    (0x10001010001000001000101000100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x101090100000000010101010000000000000000000000000000000000000000 <<< 9984) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x101000000000101010100000000010900000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000100000100010100010000010001 <<< 11520) |||
    (0x1000100000100010001000101000100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12544) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10001010001000001000101000100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000001000101000100000100010100 <<< 14080) |||
    (0x101010101010101 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010000010100000101000001010000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x1010000010100010000010107000100000000000000000000000000000000 <<< 15616) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010100010000000100000000000001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x100000100000100010100000100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1000000000107010100010001000000000000000000000000000000000000 <<< 17664) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1000000000100010107010001000000000000000000000000000000000000 <<< 18688) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010001010001010001000001010001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010100010000000001010101010100 <<< 20224) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x10101090001000001000100010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010100010000000100000000000001 <<< 21760) |||
    (0x1000101010100000000000001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10101010101000000000100010101 <<< 22784) |||
    (0x10101010101000000000100010101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10001010001000001000101000100 <<< 24832) |||
    (0x10001010001000001000101000100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x101000100000000010101010000000000000000000000000000000000000000 <<< 26368) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x101000000000101010100000000010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000100000100010100010000010001 <<< 27904) |||
    (0x1000100000100010001000101000100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x101010100070000000000000101010100000000000000000000000000000000 <<< 28928) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10001010001000001000101000100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1000001000101000100000100010100 <<< 30464) |||
    (0x101010101010101 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010000010100000101000001010000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x1010000010100010000010100000100000000000000000000000000000000 <<< 32000) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `9` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN9 : ℕ :=
    0x1000101010001010101010100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x100000100000100010100000100 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1000000070100010100010001000000000000000000000000000000000000 <<< 1280) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1000000070100010100010001000000000000000000000000000000000000 <<< 2304) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x100000100000100010100000100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1010100010000000001010101010100 <<< 3840) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101010001070001000100010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1010100010000000100000000000001 <<< 5376) |||
    (0x1010100010000000001010101010100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x10101010101000000000100010101 <<< 6400) |||
    (0x1000000000000010101010001000000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1000100000100010100010000010001 <<< 8448) |||
    (0x10001010001000001000101000100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 9984) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10001010001000001000109000100 <<< 11520) |||
    (0x1000100000100010001000101000100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 12544) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10001010001000001000101000100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x90100010000010001010001000001 <<< 14080) |||
    (0x101010101010101 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x101070001010000010100000101 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 15616) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010001010101010100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x100000100000100010100000100 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x701000000000100010100010001000000000000000000000000000000000000 <<< 17664) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x701000000000100010100010001000000000000000000000000000000000000 <<< 18688) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x100000100000100010100000100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1010100010000000001010101010100 <<< 20224) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101010001000001000107010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1010100010000000100000000000001 <<< 21760) |||
    (0x1010100010000000001010101010100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x10101010101000000000100010101 <<< 22784) |||
    (0x1000000000000010101010001000000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1000100000100010100010007010001 <<< 24832) |||
    (0x10001010001000001000101000100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 26368) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10001010001000001000100000100 <<< 27904) |||
    (0x1000100000100010001000101000100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 28928) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10001010001000001000101000100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x100010000010001010001000001 <<< 30464) |||
    (0x101010101010101 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x101000001010000010100000101 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 32000) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `10` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN10 : ℕ :=
    0x1000101010001010101010100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010001010001010001000001010001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1000000000100000100010009000000000000000000000000000000000000 <<< 1280) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1070000000100010100010001000000000000000000000000000000000000 <<< 2304) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x100000100000100010100000100 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100000000000001 <<< 3840) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100000101010009000001000100010100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010001010101010100 <<< 5376) |||
    (0x1010100010000000001010101010100 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000000000000010101010001000000 <<< 6400) |||
    (0x1000000000000010101010001000000 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10001010001000001000101000100 <<< 8448) |||
    (0x10001010001000001000101000100 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 9984) |||
    (0x1000101000100000100010900010000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000100000100010100010000010001 <<< 11520) |||
    (0x1000100000100010001000101000100 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 12544) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10001010001000001000101000100 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000001000101000100000100010100 <<< 14080) |||
    (0x101010101010101 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010000010100000101000001010000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 15616) |||
    (0x10000000101010100000101000000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010001010101010100 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010001010001010001000001010001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1000000000100090100010000000000000000000000000000000000000000 <<< 17664) |||
    (0x101010001000000000101010101010000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1000000000107010100010001000000000000000000000000000000000000 <<< 18688) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x100000100000100010100000100 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100000000000001 <<< 20224) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100090101010000000001000100010100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010001010101010100 <<< 21760) |||
    (0x1010100010000000001010101010100 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000000000000010101010001000000 <<< 22784) |||
    (0x1000000000000010101010001000000 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x100000000000001010101000100000000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10001010001000001000101000100 <<< 24832) |||
    (0x10001010001000001000101000100 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1010001000701010000010001010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 26368) |||
    (0x1000101000100000100010000010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000100000100010100010000010001 <<< 27904) |||
    (0x1000100000100010001000101000100 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 28928) |||
    (0x100010000010001010001000701000100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10001010001000001000101000100 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1000001000101000100000100010100 <<< 30464) |||
    (0x101010101010101 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010000010100000101000001010000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 32000) |||
    (0x10900000101010100000101000000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `11` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN11 : ℕ :=
    0x1010100010000000100000000000001 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1010001010001010001000001010001 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x1000000000100010100010001000700000000000000000000000000000000 <<< 1280) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x1000000000100000100010009000000000000000000000000000000000000 <<< 2304) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1010001010001010001000001010001 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100000000000001 <<< 3840) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101010001000009000100010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101010001010101010100 <<< 5376) |||
    (0x1000101010100000000000001 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1000000000000010101010001000000 <<< 6400) |||
    (0x10101010101000000000100010101 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10001010001000001000101000100 <<< 8448) |||
    (0x1000100000100010100010000010001 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 9984) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1000100000100010100010000010001 <<< 11520) |||
    (0x10001010001000100010000010001 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 12544) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1000100000100010100010000010001 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1000001000101000100000100010100 <<< 14080) |||
    (0x1010101010101010000000000000700 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1010000010100000101000001010000 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 15616) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1010100010000000100000000000001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1010001010001010001000001010001 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x1000000000100010107010001000000000000000000000000000000000000 <<< 17664) |||
    (0x100010101010000000000000100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x1000000000100090100010000000000000000000000000000000000000000 <<< 18688) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1010001010001010001000001010001 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100000000000001 <<< 20224) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101010001000000000100010900000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010001010101010100 <<< 21760) |||
    (0x1000101010100000000000001 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1000000000000010101010001000000 <<< 22784) |||
    (0x10101010101000000000100010101 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x1010101010100000000010001010100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10001010001000001000101000100 <<< 24832) |||
    (0x1000100000100010100010007010001 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1010101000000000101010100000000000000000000000000000000 <<< 26368) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1000100000100010100010000010001 <<< 27904) |||
    (0x10001010001000100010700010001 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 28928) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1000100000100010100010007010001 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1000001000101000100000100010100 <<< 30464) |||
    (0x1010101010101010000000000000000 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1010000010100000101000001010000 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x100000101000001000101000001010000000000000000000000000000000000 <<< 32000) |||
    (0x101000001010000000001010000010100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `12` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN12 : ℕ :=
    0x10101000000010000000101000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000109010000010000010001000101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 1280) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 2304) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10000000001000101000107010000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10101000000010101010000010101 <<< 3840) |||
    (0x100000109010001000001000100010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10101000000010000000101000000 <<< 5376) |||
    (0x1000000010101000000000101000000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010100000101010100000001010100 <<< 6400) |||
    (0x1010100000101010100000001010100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010000000001010101000000000101 <<< 8448) |||
    (0x1010000000001010101000000000101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x1090101010101010000000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 9984) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1000101000100000100010900010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x101010100000000010101010000 <<< 11520) |||
    (0x101010100000101000000000101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 12544) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010000000001010101000000000101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x10101010000000001010101 <<< 14080) |||
    (0x1000001010000010001010000000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10001000100010001000100010001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 15616) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10101000000010000000101000000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000100010900010000010001000101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 17664) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 18688) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10000000001000101070100010000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10101000000010101010000010101 <<< 20224) |||
    (0x100090100010001000001000100010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10101000000010000000101000000 <<< 21760) |||
    (0x1000000010101000000000101000000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010100000101010100000001010100 <<< 22784) |||
    (0x1010100000101010100000001010100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010000000001010101000000000101 <<< 24832) |||
    (0x1010000000001010101000000000101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x1000101010101010000000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 26368) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1000101000100000100010000010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x101010100000000010101010000 <<< 27904) |||
    (0x101010100000101000000000101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 28928) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010000000001010101000000000101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x700010101010000000001010101 <<< 30464) |||
    (0x1000001010000010001010000090100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10001000100010001000100010001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 32000) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `13` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN13 : ℕ :=
    0x1000000010101000101010000010101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000101010100010000090000000101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 1280) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 2304) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10000000001000101000000090000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000000010101000000000101000000 <<< 3840) |||
    (0x100010101010001000009000000010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x10101000000010000000101000000 <<< 5376) |||
    (0x10101000000010101010000010101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010000000001010100000001 <<< 6400) |||
    (0x1010100000101010100000001010100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x101010100000000010101010000 <<< 8448) |||
    (0x1010000000001010101000000000101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 9984) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x101010100000000010101010000 <<< 11520) |||
    (0x1010000000001010000010101010000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 12544) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010000000001010101000000000101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010101000000000101010100000000 <<< 14080) |||
    (0x10100000101000100000101000001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10001000100010001000100010001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10101010101000100000000000000000000000000000000 <<< 15616) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000000010101000101010000010101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000101010100010000000009000101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 17664) |||
    (0x1010100000001010101000001010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 18688) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10000000001000101000900000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000000010101000000000101000000 <<< 20224) |||
    (0x100010101010001000000000900010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x10101000000010000000101000000 <<< 21760) |||
    (0x10101000000010101010000010101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010000000001010100000001 <<< 22784) |||
    (0x1010100000101010100000001010100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x101010100000000010101010007 <<< 24832) |||
    (0x1010000000001010101000000000101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 26368) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x101010100000000010101010000 <<< 27904) |||
    (0x1010000000001010700010101010000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 28928) |||
    (0x10101010000000001010101000700000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010000000001010101000000000101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010101000000000101010100000000 <<< 30464) |||
    (0x10100000101000100000101000001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10001000100010001000100010001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10101010101090100000000000000000000000000000000 <<< 32000) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `14` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN14 : ℕ :=
    0x1000000010101000101010000010101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000001090100010000010001000101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 1280) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 2304) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10700000001000101000100010000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000000010101000000000101000000 <<< 3840) |||
    (0x100010101010001000001070100010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000000010101000101010000010101 <<< 5376) |||
    (0x1000000010101000000000101000000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010100000101010100000001010100 <<< 6400) |||
    (0x1010000000001010100000001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010000000001010101000000000101 <<< 8448) |||
    (0x101010100000000010101010000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 9984) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010000000001010101000000000109 <<< 11520) |||
    (0x101010100000101000000000101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100000100010900000101000100000100000000000000000000000000000000 <<< 12544) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010000000001010101000000000101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010101000000000101010100000000 <<< 14080) |||
    (0x10100000101000100000101000001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10001000100010001000100010001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 15616) |||
    (0x10001000100000100010001000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000000010101000101010000010101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000901000100010000010001000101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 17664) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 18688) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10000070001000101000100010000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000000010101000000000101000000 <<< 20224) |||
    (0x100010101010001000001000107010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101000101000101000100000101000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000000010101000101010000010101 <<< 21760) |||
    (0x1000000010101000000000101000000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010100000101010100000001010100 <<< 22784) |||
    (0x1010000000001010100000001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101010000010101010000000101010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010000000001010101000000000101 <<< 24832) |||
    (0x101010100000000010101010007 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1010001000001000101000100000100000000000000000000000000000000 <<< 26368) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010000000001010101000000000100 <<< 27904) |||
    (0x101010100000101000000000101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100000100010000000101000100000100000000000000000000000000000000 <<< 28928) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010000000001010101000000000101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010101000000000101010100000000 <<< 30464) |||
    (0x10100000101000100000101000001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10001000100010001000100010001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 32000) |||
    (0x900010001000100000100010001000100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `15` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN15 : ℕ :=
    0x10101000000010000000101000000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000101010100010000010701000101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 1280) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 2304) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10000000701000101000100010000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10101000000010101010000010101 <<< 3840) |||
    (0x100010901000001000001000100010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000000010101000101010000010101 <<< 5376) |||
    (0x10101000000010101010000010101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010000000001010100000001 <<< 6400) |||
    (0x1010000000001010100000001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010000000001010101000000000101 <<< 8448) |||
    (0x1010000000001010101000000000101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100000100010100010000010001010000000000000000000000000000000000 <<< 9984) |||
    (0x101000000000101010100000000010900000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x101010100000000010101010000 <<< 11520) |||
    (0x101010100000101000000000101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 12544) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x101010100000000010101010000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010101000000000101010100000000 <<< 14080) |||
    (0x10100000101000100000101000001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000100010001070100010001000100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 15616) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x10101000000010000000101000000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000101010100010000010001070101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 17664) |||
    (0x100000001010100000000010100000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 18688) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10007000001000101000100010000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10101000000010101010000010101 <<< 20224) |||
    (0x100010001090001000001000100010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x10000010000010001010000010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000000010101000101010000010101 <<< 21760) |||
    (0x10101000000010101010000010101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010000000001010100000001 <<< 22784) |||
    (0x1010000000001010100000001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000000000101010000000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010000000001010101000000000101 <<< 24832) |||
    (0x1010000000001010101000000000101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x107000100010100010000010001010000000000000000000000000000000000 <<< 26368) |||
    (0x101000000000101010100000000010000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x101010100000000010101010000 <<< 27904) |||
    (0x101010100000101000000000101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 28928) |||
    (0x101000000000101010100000000010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x101010100000000010101010007 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010101000000000101010100000000 <<< 30464) |||
    (0x10100000101000100000101000001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000100010001000100010001000100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101010101010101000000000000000000000000000000000000000000000000 <<< 32000) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `16` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN16 : ℕ :=
    0x30000030300030000030000030000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x3000000000000030000000300030303 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 1280) |||
    (0x3000003030003030300030300030300000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 2304) |||
    (0x300030300000300030300030300030300000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x30303030303000303030003000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x30000030300030303000303000303 <<< 3840) |||
    (0x300000000000003000000030003030300000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x30000030300030000030000030000 <<< 5376) |||
    (0x3000303000003000000030000030000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x3030003030003030300030300000300 <<< 6400) |||
    (0x3030003030003030300030300000300 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x30000030000000300000303000300000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0xb000000000b000b00000b001b000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x303030303030303030b030303030303 <<< 8448) |||
    (0x303030303030303030b030303030303 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x30b00000303030300000303000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x300030003000b000300030003000300000000000000000000000000000000 <<< 9984) |||
    (0x0 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x303000003030000030b000003030000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x0 <<< 11520) |||
    (0x303030303030b03 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x3000300030003030003000300030000000000000000000000000000000000 <<< 12544) |||
    (0x303030303030303030b03030303030300000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x303030303030303030b030303030303 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x303000003030000030300000303 <<< 14080) |||
    (0x3000300000300030003000003000300 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x300030000030003030003000003 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x303000000000303050003030303000000000000000000000000000000000000 <<< 15616) |||
    (0x3030003000503030000030003030000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x30000030300030000030000030000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x3000000000000030000000300030303 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 17664) |||
    (0x3000003030003030300030300030300000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 18688) |||
    (0x300030300000300030300030300030300000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x30303030303000303030003000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x30000030300030303000303000303 <<< 20224) |||
    (0x300000000000003000000030003030300000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x30000030300030000030000030000 <<< 21760) |||
    (0x3000303000003000000030000030000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x3030003030003030300030300000300 <<< 22784) |||
    (0x3030003030003030300030300000300 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x30000030000000300000303000300000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0xb00000000000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x3030303030303030300030303030303 <<< 24832) |||
    (0x3030303030303030300030303030303 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x30000000303030300000303000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x3000300030000000300030003000300000000000000000000000000000000 <<< 26368) |||
    (0x500000000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x3030000030300000300000003030000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x5000000000000 <<< 27904) |||
    (0x303030303030003 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x503000300030003030003000300030000000000000000000000000000000000 <<< 28928) |||
    (0x303030303030303030003030303030300000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x3030303030303030300030303030303 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x303050003030000030300000303 <<< 30464) |||
    (0x3000300000300030003000b03000300 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0xb0300030000030003030003000003 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x303000000000303000003030303000000000000000000000000000000000000 <<< 32000) |||
    (0x3030003000003030000030003030000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `17` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN17 : ℕ :=
    0x30000030300030000030000030000 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x3000000000000030000000300030303 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 1280) |||
    (0x3000003030003030300030300030300000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 2304) |||
    (0x300030300000300030300030300030300000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x30303030303000303030003000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x30000030300030303000303000303 <<< 3840) |||
    (0x300000000000003000000030003030300000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x30000030300030000030000030000 <<< 5376) |||
    (0x3000303000003000000030000030000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x3030003030003030300030300000300 <<< 6400) |||
    (0x3030003030003030300030300000300 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x30000030000000300000303000300000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0xb000000000b000b00000b001b000000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x303030303030303030b030303030303 <<< 8448) |||
    (0x303030303030303030b030303030303 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x30b00000303030300000303000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x300030003000b000300030003000300000000000000000000000000000000 <<< 9984) |||
    (0x0 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x303000003030000030b000003030000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x0 <<< 11520) |||
    (0x303030303030b03 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x3000300030003030003000300030000000000000000000000000000000000 <<< 12544) |||
    (0x303030303030303030b03030303030300000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x303030303030303030b030303030303 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x303000003030000030300000303 <<< 14080) |||
    (0x3000300000300030003000003000300 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x300030000030003030003000003 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x303000000000303050003030303000000000000000000000000000000000000 <<< 15616) |||
    (0x3030003000503030000030003030000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x30000030300030000030000030000 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x3000000000000030000000300030303 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 17664) |||
    (0x3000003030003030300030300030300000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x303030000030303000303030000000300000000000000000000000000000000 <<< 18688) |||
    (0x300030300000300030300030300030300000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x30303030303000303030003000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x30000030300030303000303000303 <<< 20224) |||
    (0x300000000000003000000030003030300000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x303000000030000000303030000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x30000030300030000030000030000 <<< 21760) |||
    (0x3000303000003000000030000030000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x3030003030003030300030300000300 <<< 22784) |||
    (0x3030003030003030300030300000300 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x30000030000000300000303000300000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0xb00000000000000000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x3030303030303030300030303030303 <<< 24832) |||
    (0x3030303030303030300030303030303 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x30000000303030300000303000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x3000300030000000300030003000300000000000000000000000000000000 <<< 26368) |||
    (0x500000000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x3030000030300000300000003030000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x5000000000000 <<< 27904) |||
    (0x303030303030003 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x503000300030003030003000300030000000000000000000000000000000000 <<< 28928) |||
    (0x303030303030303030003030303030300000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x3030303030303030300030303030303 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x303050003030000030300000303 <<< 30464) |||
    (0x3000300000300030003000b03000300 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0xb0300030000030003030003000003 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x303000000000303000003030303000000000000000000000000000000000000 <<< 32000) |||
    (0x3030003000003030000030003030000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `18` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN18 : ℕ :=
    0x1000101000001000101000101000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101010101000101010001000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 1280) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 2304) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000000000010000000100010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101000001000000010000010000 <<< 3840) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000101000001000101000101000101 <<< 5376) |||
    (0x10000010100010101000101000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100000100000001000001010001 <<< 6400) |||
    (0x100000100000001000001010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x900000909000009000009000000090000000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101010101010101010101010101 <<< 8448) |||
    (0x1010101010101010101010101010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 9984) |||
    (0x0 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x0 <<< 11520) |||
    (0x101010101010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 12544) |||
    (0x101010101010101010101010101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101010101010101010101010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101000001010000010100000101 <<< 14080) |||
    (0x1000100000100010001000101000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100010000010001010001000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 15616) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101000001000101000101000101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101010101000101010001000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 17664) |||
    (0x100010100000100000001000001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101000000010000000101010000000000000000000000000000000000 <<< 18688) |||
    (0x1000001010001000001000001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000000000010000000100010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101000001000000010000010000 <<< 20224) |||
    (0x1010101010100010101000100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010000010101000101010000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101000001000101000101000101 <<< 21760) |||
    (0x10000010100010101000101000101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100000100000001000001010001 <<< 22784) |||
    (0x100000100000001000001010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000101000101010001010000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x90000090000000000000900000900000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101010101010101010101010101 <<< 24832) |||
    (0x1010101010101010101010101010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10100000101010100000101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000100010001000100010001000100000000000000000000000000000000 <<< 26368) |||
    (0x0 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010000010100000101000001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x0 <<< 27904) |||
    (0x101010101010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000100010001010001000100010000000000000000000000000000000000 <<< 28928) |||
    (0x101010101010101010101010101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101010101010101010101010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101000001010000010100000101 <<< 30464) |||
    (0x1000100000100010001000101000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100010000010001010001000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000000000101000001010101000000000000000000000000000000000000 <<< 32000) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `19` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN19 : ℕ :=
    0x5000505000005000505000505000505 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x50505050505000505050005000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x505000000050000000505050000000000000000000000000000000000 <<< 1280) |||
    (0x500050500000500000005000005000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x505000000050000000505050000000000000000000000000000000000 <<< 2304) |||
    (0x5000005050005000005000005000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x5000000000000050000000500050505 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x5000505000005000000050000050000 <<< 3840) |||
    (0x5050505050500050505000500000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x505050000050505000505050000000500000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x5000505000005000505000505000505 <<< 5376) |||
    (0x50000050500050505000505000505 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x500000500000005000005050005 <<< 6400) |||
    (0x500000500000005000005050005 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x505000505000505050005050000050000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x500050505050005001305000500050500000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x0 <<< 8448) |||
    (0x0 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x505000005050000000005050000050500000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x500050005000500050005000500050000000000000000000000000000000000 <<< 9984) |||
    (0x505050505050505051d05050505050500000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x500000505000005050000050500000500000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x505050505050505051d050505050505 <<< 11520) |||
    (0x5050505050505050000000000000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1d00050005000500000500050005000500000000000000000000000000000000 <<< 12544) |||
    (0x0 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x0 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x50500001d0500000505000005050000 <<< 14080) |||
    (0x50005050005000500051300050005 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x5130005000505000500000500050500 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x50505050000000500000000050500000000000000000000000000000000 <<< 15616) |||
    (0x500000500050000000505000500000500000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x5000505000005000505000505000505 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x50505050505000505050005000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x505000000050000000505050000000000000000000000000000000000 <<< 17664) |||
    (0x500050500000500000005000005000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x505000000050000000505050000000000000000000000000000000000 <<< 18688) |||
    (0x5000005050005000005000005000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x5000000000000050000000500050505 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x5000505000005000000050000050000 <<< 20224) |||
    (0x5050505050500050505000500000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x505050000050505000505050000000500000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x5000505000005000505000505000505 <<< 21760) |||
    (0x50000050500050505000505000505 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x500000500000005000005050005 <<< 22784) |||
    (0x500000500000005000005050005 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x505000505000505050005050000050000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x513050505051305130005130503050500000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x13000000000000 <<< 24832) |||
    (0x13000000000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x505001305050000000005050000050500000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x500050005000513050005000500050000000000000000000000000000000000 <<< 26368) |||
    (0x505050505050505050005050505050500000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x500000505000005050013050500000500000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x5050505050505050500050505050505 <<< 27904) |||
    (0x5050505050505050000000000001300 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x50005000500000500050005000500000000000000000000000000000000 <<< 28928) |||
    (0x1300000000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x13000000000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x5050000000500000505000005050000 <<< 30464) |||
    (0x50005050005000500050000050005 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x5000005000505000500000500050500 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x505050500001d0500000000050500000000000000000000000000000000 <<< 32000) |||
    (0x500000500051d00000505000500000500000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `20` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN20 : ℕ :=
    0x1000109010100010000010001000100 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x1070000000100010100010001000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100010101000100010000 <<< 3840) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x9000101010100010000010000000101 <<< 5376) |||
    (0x10000000001000000010001000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010100010101010001 <<< 6400) |||
    (0x100010001010100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010101010100000000 <<< 8448) |||
    (0x10101010101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x101000000000101010100000000010900000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000000000001010101 <<< 11520) |||
    (0x1010901000000000101010100000000 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x100010000010001010001000001000100000000000000000000000000000000 <<< 12544) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010000010101010000 <<< 14080) |||
    (0x10001000100010001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x1000001010000010001010000000100 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000100010100010000010001000109 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x1000000000100010100010001070000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100010101000100010000 <<< 20224) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x101010100010000010009000101 <<< 21760) |||
    (0x10000000001000000010001000101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010100010101010001 <<< 22784) |||
    (0x100010001010100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10101010101010100000000 <<< 24832) |||
    (0x10101010101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x101000000000101010100000000010000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 26368) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000000000000000001010101 <<< 27904) |||
    (0x1010001000000000101010100000000 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x100010000010001010001000701000100000000000000000000000000000000 <<< 28928) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10101010101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010000010101010000 <<< 30464) |||
    (0x10001000100010001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x1000001010000010001010000090100 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `21` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN21 : ℕ :=
    0x1070101010100010000010001000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x10101000000010000000101000000 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 2304) |||
    (0x1000000000100010100010001000700000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000001000000010001000101 <<< 3840) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000109010100010000010001000100 <<< 5376) |||
    (0x10000000001000000010001000101 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000001000000000100 <<< 6400) |||
    (0x1010001000100000001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010101010100000000 <<< 8448) |||
    (0x10101010101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x1000101000100010001000001000100000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x10901010101010100000000 <<< 11520) |||
    (0x10101010000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 12544) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010000010101010000 <<< 14080) |||
    (0x1000100010001070100010001000100 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000100000101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000101010100010000010001070101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x10101000000010000000101000000 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 18688) |||
    (0x1000700000100010100010001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000001000000010001000101 <<< 20224) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000100010100010000010001000109 <<< 21760) |||
    (0x10000000001000000010001000101 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000001000000000100 <<< 22784) |||
    (0x1010001000100000001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x101000100010000000100000000010000000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10101010101010100000000 <<< 24832) |||
    (0x10101010101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x1000101000100010001070001000100000000000000000000000000000000 <<< 26368) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x10001010101010100000000 <<< 27904) |||
    (0x10101010000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 28928) |||
    (0x101010100070000000000000101010100000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10101010101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010000010101010000 <<< 30464) |||
    (0x1000100010001000100010001000100 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `22` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN22 : ℕ :=
    0x1000001010100010000010001000901 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 1280) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x100010100010009000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x10101000000010000000101000000 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x1000101010100010101000100010000 <<< 3840) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1000001010100010000010001000901 <<< 5376) |||
    (0x1000101010100010101000100010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x1010001000100000001000000000100 <<< 6400) |||
    (0x100010001010100010101010001 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x1010101000000000000000001010101 <<< 8448) |||
    (0x10101010101010100000000 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 9984) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x1010001000001010000010001010000000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000000000001010101 <<< 11520) |||
    (0x10101010000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 12544) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x1010101000000000000000001010101 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x1010000000001010000010101010000 <<< 14080) |||
    (0x10001000100010001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000100000101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 15616) |||
    (0x1010000010100000100000001010000000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x1000901010100010000010001000001 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 17664) |||
    (0x1000000000100000001000100010100000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x9000000000100010100010000000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x10101000000010000000101000000 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x1000101010100010101000100010000 <<< 20224) |||
    (0x1010100000001000000010100000000000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x100010101000101010101010000000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000901010100010000010001000001 <<< 21760) |||
    (0x1000101010100010101000100010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x1010001000100000001000000000100 <<< 22784) |||
    (0x100010001010100010101010001 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x1010101000700000000000001010101 <<< 24832) |||
    (0x10101010101010100000000 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 26368) |||
    (0x101010100000000000000000101010100000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x1010001000701010000010001010000000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000000000000000001010101 <<< 27904) |||
    (0x10101010000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 28928) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x1010101000700000000000001010101 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x1010000000001010000010101010000 <<< 30464) |||
    (0x10001000100010001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x10100000101000001010000010100000000000000000000000000000000 <<< 32000) |||
    (0x1010000010100000109000001010000000000000000000000000000000000 <<< 32256)

/-- The negative parts of column `23` of the Sixth tensor numerators (`8`-bit fields). -/
@[irreducible] def sixthSXN23 : ℕ :=
    0x9000101010100010000010000000101 |||
    (0x0 <<< 256) |||
    (0x0 <<< 512) |||
    (0x1000000010101000101010000010101 <<< 768) |||
    (0x0 <<< 1024) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 1280) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 1536) |||
    (0x0 <<< 1792) |||
    (0x0 <<< 2048) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 2304) |||
    (0x1000000000100010100010701000000000000000000000000000000000000 <<< 2560) |||
    (0x0 <<< 2816) |||
    (0x1000000010101000101010000010101 <<< 3072) |||
    (0x0 <<< 3328) |||
    (0x0 <<< 3584) |||
    (0x10000000001000000010001000101 <<< 3840) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 4096) |||
    (0x0 <<< 4352) |||
    (0x0 <<< 4608) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 4864) |||
    (0x0 <<< 5120) |||
    (0x1070101010100010000010001000101 <<< 5376) |||
    (0x1000101010100010101000100010000 <<< 5632) |||
    (0x0 <<< 5888) |||
    (0x0 <<< 6144) |||
    (0x100010001010100010101010001 <<< 6400) |||
    (0x1010001000100000001000000000100 <<< 6656) |||
    (0x0 <<< 6912) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 7168) |||
    (0x0 <<< 7424) |||
    (0x0 <<< 7680) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 7936) |||
    (0x0 <<< 8192) |||
    (0x10101010101010100000000 <<< 8448) |||
    (0x1010101000000000000000001010101 <<< 8704) |||
    (0x0 <<< 8960) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 9216) |||
    (0x0 <<< 9472) |||
    (0x0 <<< 9728) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 9984) |||
    (0x1090101010101010000000000000000000000000000000000000000 <<< 10240) |||
    (0x0 <<< 10496) |||
    (0x0 <<< 10752) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 11008) |||
    (0x0 <<< 11264) |||
    (0x1010101000000000000000001010101 <<< 11520) |||
    (0x10101010000000001010101 <<< 11776) |||
    (0x0 <<< 12032) |||
    (0x0 <<< 12288) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 12544) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 12800) |||
    (0x0 <<< 13056) |||
    (0x10101010101010100000000 <<< 13312) |||
    (0x0 <<< 13568) |||
    (0x0 <<< 13824) |||
    (0x101010100000901000000000101 <<< 14080) |||
    (0x10001000100010001000100010001 <<< 14336) |||
    (0x0 <<< 14592) |||
    (0x0 <<< 14848) |||
    (0x10100000101000100000101000001 <<< 15104) |||
    (0x0 <<< 15360) |||
    (0x101000000010000010100000101000000000000000000000000000000000000 <<< 15616) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 15872) |||
    (0x0 <<< 16128) |||
    (0x101010100010000010009000101 <<< 16384) |||
    (0x0 <<< 16640) |||
    (0x0 <<< 16896) |||
    (0x1000000010101000101010000010101 <<< 17152) |||
    (0x0 <<< 17408) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 17664) |||
    (0x100010101010001010100010001000000000000000000000000000000000000 <<< 17920) |||
    (0x0 <<< 18176) |||
    (0x0 <<< 18432) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 18688) |||
    (0x701000000000100010100010001000000000000000000000000000000000000 <<< 18944) |||
    (0x0 <<< 19200) |||
    (0x1000000010101000101010000010101 <<< 19456) |||
    (0x0 <<< 19712) |||
    (0x0 <<< 19968) |||
    (0x10000000001000000010001000101 <<< 20224) |||
    (0x100000001010100010101000001010100000000000000000000000000000000 <<< 20480) |||
    (0x0 <<< 20736) |||
    (0x0 <<< 20992) |||
    (0x101010001000000010000000000000100000000000000000000000000000000 <<< 21248) |||
    (0x0 <<< 21504) |||
    (0x1000101010100010000010001070101 <<< 21760) |||
    (0x1000101010100010101000100010000 <<< 22016) |||
    (0x0 <<< 22272) |||
    (0x0 <<< 22528) |||
    (0x100010001010100010101010001 <<< 22784) |||
    (0x1010001000100000001000000000100 <<< 23040) |||
    (0x0 <<< 23296) |||
    (0x10001000101010001010101000100000000000000000000000000000000 <<< 23552) |||
    (0x0 <<< 23808) |||
    (0x0 <<< 24064) |||
    (0x100010100000100010100010100010100000000000000000000000000000000 <<< 24320) |||
    (0x0 <<< 24576) |||
    (0x10101010101010100000000 <<< 24832) |||
    (0x1010101000700000000000001010101 <<< 25088) |||
    (0x0 <<< 25344) |||
    (0x10101010000000001010101000000000000000000000000000000000000 <<< 25600) |||
    (0x0 <<< 25856) |||
    (0x0 <<< 26112) |||
    (0x100010000010001000100010100010000000000000000000000000000000000 <<< 26368) |||
    (0x1000101010101010000000000000000000000000000000000000000 <<< 26624) |||
    (0x0 <<< 26880) |||
    (0x0 <<< 27136) |||
    (0x100000100010100000101000100000100000000000000000000000000000000 <<< 27392) |||
    (0x0 <<< 27648) |||
    (0x1010101000000000000000001010101 <<< 27904) |||
    (0x10101010000000001010101 <<< 28160) |||
    (0x0 <<< 28416) |||
    (0x0 <<< 28672) |||
    (0x1000101000100000100010100010000000000000000000000000000000000 <<< 28928) |||
    (0x1010101010101010000000000000000000000000000000000000000 <<< 29184) |||
    (0x0 <<< 29440) |||
    (0x10101010101010100000000 <<< 29696) |||
    (0x0 <<< 29952) |||
    (0x0 <<< 30208) |||
    (0x101010100000001000000000101 <<< 30464) |||
    (0x10001000100010001000100010001 <<< 30720) |||
    (0x0 <<< 30976) |||
    (0x0 <<< 31232) |||
    (0x10100000101000100000101000001 <<< 31488) |||
    (0x0 <<< 31744) |||
    (0x101000009010000010100000101000000000000000000000000000000000000 <<< 32000) |||
    (0x100000101000001010000010100000100000000000000000000000000000000 <<< 32256)

/-- The negative parts of the columns. -/
def sixthSXN : List ℕ :=
  [sixthSXN0, sixthSXN1, sixthSXN2, sixthSXN3, sixthSXN4, sixthSXN5, sixthSXN6, sixthSXN7,
    sixthSXN8, sixthSXN9, sixthSXN10, sixthSXN11, sixthSXN12, sixthSXN13, sixthSXN14, sixthSXN15,
    sixthSXN16, sixthSXN17, sixthSXN18, sixthSXN19, sixthSXN20, sixthSXN21, sixthSXN22,
    sixthSXN23]

/-- The packed Sixth tensor at width `w`, from the compact columns. -/
def sixthSXF (w : ℕ) : List SVec :=
  (List.range 24).map (fun j =>
    (respace 8 w 12 (sixthSXP.getD j 0), respace 8 w 12 (sixthSXN.getD j 0)))

/-- The check of one compact column: sizes and values against the fast numerators. -/
def sixthColOk (j : ℕ) : Bool :=
  decide (sixthSXP.getD j 0 < 2 ^ (8 * 2 ^ 12)) && decide (sixthSXN.getD j 0 < 2 ^ (8 * 2 ^ 12)) &&
    (List.range (2 ^ 12)).all (fun k =>
      decide ((fld 8 (sixthSXP.getD j 0) k : ℤ) - fld 8 (sixthSXN.getD j 0) k = sixthTNumF k j))

/-- A checked column at any width `w ≥ 8`: field bound `2 ^ 8 - 1` and the fast numerators. -/
theorem sixthColOk_spec {w j : ℕ} (hw : 8 ≤ w) (hj : j < 24) (h : sixthColOk j = true) :
    SBnd w (2 ^ 12) (2 ^ 8 - 1) (tcol (sixthSXF w) j) ∧
      ∀ k < 2 ^ 12, sval w (tcol (sixthSXF w) j) k = sixthTNumF k j := by
  simp only [sixthColOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hP, hN⟩, hv⟩ := h
  obtain ⟨c1, c2⟩ := respace_col hw hP hN
  rw [sixthSXF, tcol_range_map _ 24 j hj]
  exact ⟨c1, fun k hk => (c2 k hk).trans (hv k hk)⟩

set_option maxRecDepth 100000 in
/-- Column `0` of the compact Sixth tensor. -/
theorem sixthColOk0 : sixthColOk 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `1` of the compact Sixth tensor. -/
theorem sixthColOk1 : sixthColOk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `2` of the compact Sixth tensor. -/
theorem sixthColOk2 : sixthColOk 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `3` of the compact Sixth tensor. -/
theorem sixthColOk3 : sixthColOk 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `4` of the compact Sixth tensor. -/
theorem sixthColOk4 : sixthColOk 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `5` of the compact Sixth tensor. -/
theorem sixthColOk5 : sixthColOk 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `6` of the compact Sixth tensor. -/
theorem sixthColOk6 : sixthColOk 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `7` of the compact Sixth tensor. -/
theorem sixthColOk7 : sixthColOk 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `8` of the compact Sixth tensor. -/
theorem sixthColOk8 : sixthColOk 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `9` of the compact Sixth tensor. -/
theorem sixthColOk9 : sixthColOk 9 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `10` of the compact Sixth tensor. -/
theorem sixthColOk10 : sixthColOk 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `11` of the compact Sixth tensor. -/
theorem sixthColOk11 : sixthColOk 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `12` of the compact Sixth tensor. -/
theorem sixthColOk12 : sixthColOk 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `13` of the compact Sixth tensor. -/
theorem sixthColOk13 : sixthColOk 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `14` of the compact Sixth tensor. -/
theorem sixthColOk14 : sixthColOk 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `15` of the compact Sixth tensor. -/
theorem sixthColOk15 : sixthColOk 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `16` of the compact Sixth tensor. -/
theorem sixthColOk16 : sixthColOk 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `17` of the compact Sixth tensor. -/
theorem sixthColOk17 : sixthColOk 17 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `18` of the compact Sixth tensor. -/
theorem sixthColOk18 : sixthColOk 18 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `19` of the compact Sixth tensor. -/
theorem sixthColOk19 : sixthColOk 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `20` of the compact Sixth tensor. -/
theorem sixthColOk20 : sixthColOk 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `21` of the compact Sixth tensor. -/
theorem sixthColOk21 : sixthColOk 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `22` of the compact Sixth tensor. -/
theorem sixthColOk22 : sixthColOk 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Column `23` of the compact Sixth tensor. -/
theorem sixthColOk23 : sixthColOk 23 = true := by decide +kernel

/-- All compact columns are checked. -/
theorem sixthColOk_all (j : ℕ) (hj : j < 24) : sixthColOk j = true := by
  interval_cases j
  · exact sixthColOk0
  · exact sixthColOk1
  · exact sixthColOk2
  · exact sixthColOk3
  · exact sixthColOk4
  · exact sixthColOk5
  · exact sixthColOk6
  · exact sixthColOk7
  · exact sixthColOk8
  · exact sixthColOk9
  · exact sixthColOk10
  · exact sixthColOk11
  · exact sixthColOk12
  · exact sixthColOk13
  · exact sixthColOk14
  · exact sixthColOk15
  · exact sixthColOk16
  · exact sixthColOk17
  · exact sixthColOk18
  · exact sixthColOk19
  · exact sixthColOk20
  · exact sixthColOk21
  · exact sixthColOk22
  · exact sixthColOk23

/-- The field bound of the fast Sixth tensor at any width `w ≥ 8`. -/
theorem sixthSXF_bnd {w : ℕ} (hw : 8 ≤ w) : TBnd w (2 ^ 8 - 1) (sixthSXF w) :=
  fun i hi => (sixthColOk_spec hw hi (sixthColOk_all i hi)).1

/-- The fast Sixth tensor satisfies the tensor bound of `sixthSrcXW_bnd`. -/
theorem sixthSXF_bnd64 {w : ℕ} (hw : 8 ≤ w) : TBnd w (4096 * 64) (sixthSXF w) :=
  fun i hi => ((sixthColOk_spec hw hi (sixthColOk_all i hi)).1).mono (by norm_num)

/-- The fast Sixth tensor has the rational tensor of the Sixth source (any `w ≥ 19`). -/
theorem sixthSXF_ten {w : ℕ} (hw : 19 ≤ w) :
    tensorRat w (sixthSXF w) 32 = tensorRat w (sixthSrcXW w) 32 := by
  funext k i
  simp only [tensorRat]
  rw [sixthSrcXW_val hw k i,
    (sixthColOk_spec (by omega) i.isLt (sixthColOk_all i.val i.isLt)).2 k.val
      (lt_of_lt_of_le k.isLt (by norm_num)), sixthTNumF_eq]

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
