/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation

/-! Candidate full signed short-image addresses for original corrected monomial word 1.
They assert no correctness until checked against the actual Q images and numerators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000
-- Each candidate row has at most64 literal addresses; row names bound vector elaboration.

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row0 : Fin 64 → ℕ :=
  ![4096, 4097, 4100, 4101, 4098, 4099, 4102, 4103,
    4104, 4105, 4108, 4109, 4106, 4107, 4110, 4111,
    12351, 12350, 12347, 12346, 12349, 12348, 12345, 12344,
    12343, 12342, 12339, 12338, 12341, 12340, 12337, 12336,
    4128, 4129, 4132, 4133, 4130, 4131, 4134, 4135,
    4136, 4137, 4140, 4141, 4138, 4139, 4142, 4143,
    12319, 12318, 12315, 12314, 12317, 12316, 12313, 12312,
    12311, 12310, 12307, 12306, 12309, 12308, 12305, 12304]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row1 : Fin 64 → ℕ :=
  ![13568, 5431, 5437, 13578, 5435, 13580, 13574, 5425,
    5438, 13577, 13571, 5428, 13573, 5426, 5432, 13583,
    5439, 13576, 13570, 5429, 13572, 5427, 5433, 13582,
    13569, 5430, 5436, 13579, 5434, 13581, 13575, 5424,
    13615, 5400, 5394, 13605, 5396, 13603, 13609, 5406,
    5393, 13606, 13612, 5403, 13610, 5405, 5399, 13600,
    5392, 13607, 13613, 5402, 13611, 5404, 5398, 13601,
    13614, 5401, 5395, 13604, 5397, 13602, 13608, 5407]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row2 : Fin 64 → ℕ :=
  ![13504, 13521, 5332, 5317, 5330, 5315, 13510, 13527,
    13528, 13513, 5324, 5341, 5322, 5339, 13534, 13519,
    5360, 5345, 13540, 13557, 13538, 13555, 5366, 5351,
    5352, 5369, 13564, 13549, 13562, 13547, 5358, 5375,
    13551, 13566, 5371, 5354, 5373, 5356, 13545, 13560,
    13559, 13542, 5347, 5362, 5349, 5364, 13553, 13536,
    5343, 5326, 13515, 13530, 13517, 13532, 5337, 5320,
    5319, 5334, 13523, 13506, 13525, 13508, 5313, 5328]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row3 : Fin 64 → ℕ :=
  ![4288, 4305, 4306, 4291, 4308, 4293, 4294, 4311,
    4312, 4297, 4298, 4315, 4300, 4317, 4318, 4303,
    4304, 4289, 4290, 4307, 4292, 4309, 4310, 4295,
    4296, 4313, 4314, 4299, 4316, 4301, 4302, 4319,
    12527, 12542, 12541, 12524, 12539, 12522, 12521, 12536,
    12535, 12518, 12517, 12532, 12515, 12530, 12529, 12512,
    12543, 12526, 12525, 12540, 12523, 12538, 12537, 12520,
    12519, 12534, 12533, 12516, 12531, 12514, 12513, 12528]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row4 : Fin 64 → ℕ :=
  ![4352, 12562, 12561, 4355, 4376, 12554, 12553, 4379,
    4372, 12550, 12549, 4375, 4364, 12574, 12573, 4367,
    4368, 12546, 12545, 4371, 4360, 12570, 12569, 4363,
    4356, 12566, 12565, 4359, 4380, 12558, 12557, 4383,
    12591, 4413, 4414, 12588, 12599, 4389, 4390, 12596,
    12603, 4393, 4394, 12600, 12579, 4401, 4402, 12576,
    12607, 4397, 4398, 12604, 12583, 4405, 4406, 12580,
    12587, 4409, 4410, 12584, 12595, 4385, 4386, 12592]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row5 : Fin 64 → ℕ :=
  ![13056, 13073, 13074, 13059, 4888, 4873, 4874, 4891,
    4884, 4869, 4870, 4887, 13068, 13085, 13086, 13071,
    4880, 4865, 4866, 4883, 13064, 13081, 13082, 13067,
    13060, 13077, 13078, 13063, 4892, 4877, 4878, 4895,
    13103, 13118, 13117, 13100, 4919, 4902, 4901, 4916,
    4923, 4906, 4905, 4920, 13091, 13106, 13105, 13088,
    4927, 4910, 4909, 4924, 13095, 13110, 13109, 13092,
    13099, 13114, 13113, 13096, 4915, 4898, 4897, 4912]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row6 : Fin 64 → ℕ :=
  ![12992, 4818, 4817, 12995, 4820, 12998, 12997, 4823,
    4824, 13002, 13001, 4827, 13004, 4830, 4829, 13007,
    4816, 12994, 12993, 4819, 12996, 4822, 4821, 12999,
    13000, 4826, 4825, 13003, 4828, 13006, 13005, 4831,
    13039, 4861, 4862, 13036, 4859, 13033, 13034, 4856,
    4855, 13029, 13030, 4852, 13027, 4849, 4850, 13024,
    4863, 13037, 13038, 4860, 13035, 4857, 4858, 13032,
    13031, 4853, 4854, 13028, 4851, 13025, 13026, 4848]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row7 : Fin 64 → ℕ :=
  ![5632, 5666, 5665, 5635, 13860, 13830, 13829, 13863,
    5672, 5642, 5641, 5675, 13836, 13870, 13869, 13839,
    13855, 13885, 13886, 13852, 5691, 5657, 5658, 5688,
    13879, 13845, 13846, 13876, 5651, 5681, 5682, 5648,
    5664, 5634, 5633, 5667, 13828, 13862, 13861, 13831,
    5640, 5674, 5673, 5643, 13868, 13838, 13837, 13871,
    13887, 13853, 13854, 13884, 5659, 5689, 5690, 5656,
    13847, 13877, 13878, 13844, 5683, 5649, 5650, 5680]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row8 : Fin 64 → ℕ :=
  ![5568, 13778, 13777, 5571, 13780, 5574, 5573, 13783,
    5592, 13770, 13769, 5595, 13772, 5598, 5597, 13775,
    13807, 5629, 5630, 13804, 5627, 13801, 13802, 5624,
    13815, 5605, 5606, 13812, 5603, 13809, 13810, 5600,
    5584, 13762, 13761, 5587, 13764, 5590, 5589, 13767,
    5576, 13786, 13785, 5579, 13788, 5582, 5581, 13791,
    13823, 5613, 5614, 13820, 5611, 13817, 13818, 5608,
    13799, 5621, 5622, 13796, 5619, 13793, 13794, 5616]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row9 : Fin 64 → ℕ :=
  ![5504, 13714, 13713, 5507, 5524, 13702, 13701, 5527,
    13720, 5514, 5513, 13723, 13708, 5534, 5533, 13711,
    13743, 5565, 5566, 13740, 13755, 5545, 5546, 13752,
    5559, 13733, 13734, 5556, 5539, 13745, 13746, 5536,
    5520, 13698, 13697, 5523, 5508, 13718, 13717, 5511,
    13704, 5530, 5529, 13707, 13724, 5518, 5517, 13727,
    13759, 5549, 5550, 13756, 13739, 5561, 5562, 13736,
    5543, 13749, 13750, 5540, 5555, 13729, 13730, 5552]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row10 : Fin 64 → ℕ :=
  ![5440, 5474, 5473, 5443, 5476, 5446, 5445, 5479,
    13672, 13642, 13641, 13675, 13644, 13678, 13677, 13647,
    13663, 13693, 13694, 13660, 13691, 13657, 13658, 13688,
    5495, 5461, 5462, 5492, 5459, 5489, 5490, 5456,
    5472, 5442, 5441, 5475, 5444, 5478, 5477, 5447,
    13640, 13674, 13673, 13643, 13676, 13646, 13645, 13679,
    13695, 13661, 13662, 13692, 13659, 13689, 13690, 13656,
    5463, 5493, 5494, 5460, 5491, 5457, 5458, 5488]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row11 : Fin 64 → ℕ :=
  ![12672, 12690, 12689, 12675, 12692, 12678, 12677, 12695,
    12696, 12682, 12681, 12699, 12684, 12702, 12701, 12687,
    4496, 4482, 4481, 4499, 4484, 4502, 4501, 4487,
    4488, 4506, 4505, 4491, 4508, 4494, 4493, 4511,
    12719, 12733, 12734, 12716, 12731, 12713, 12714, 12728,
    12727, 12709, 12710, 12724, 12707, 12721, 12722, 12704,
    4543, 4525, 4526, 4540, 4523, 4537, 4538, 4520,
    4519, 4533, 4534, 4516, 4531, 4513, 4514, 4528]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row12 : Fin 64 → ℕ :=
  ![12608, 4433, 4434, 12611, 12632, 4425, 4426, 12635,
    12628, 4421, 4422, 12631, 12620, 4445, 4446, 12623,
    4432, 12609, 12610, 4435, 4424, 12633, 12634, 4427,
    4420, 12629, 12630, 4423, 4444, 12621, 12622, 4447,
    12655, 4478, 4477, 12652, 12663, 4454, 4453, 12660,
    12667, 4458, 4457, 12664, 12643, 4466, 4465, 12640,
    4479, 12654, 12653, 4476, 4455, 12662, 12661, 4452,
    4459, 12666, 12665, 4456, 4467, 12642, 12641, 4464]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row13 : Fin 64 → ℕ :=
  ![4928, 4946, 4945, 4931, 13144, 13130, 13129, 13147,
    13140, 13126, 13125, 13143, 4940, 4958, 4957, 4943,
    4944, 4930, 4929, 4947, 13128, 13146, 13145, 13131,
    13124, 13142, 13141, 13127, 4956, 4942, 4941, 4959,
    13167, 13181, 13182, 13164, 4983, 4965, 4966, 4980,
    4987, 4969, 4970, 4984, 13155, 13169, 13170, 13152,
    13183, 13165, 13166, 13180, 4967, 4981, 4982, 4964,
    4971, 4985, 4986, 4968, 13171, 13153, 13154, 13168]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row14 : Fin 64 → ℕ :=
  ![4992, 13201, 13202, 4995, 13204, 4997, 4998, 13207,
    13208, 5001, 5002, 13211, 5004, 13213, 13214, 5007,
    5008, 13185, 13186, 5011, 13188, 5013, 5014, 13191,
    13192, 5017, 5018, 13195, 5020, 13197, 13198, 5023,
    13231, 5054, 5053, 13228, 5051, 13226, 13225, 5048,
    5047, 13222, 13221, 5044, 13219, 5042, 5041, 13216,
    13247, 5038, 5037, 13244, 5035, 13242, 13241, 5032,
    5031, 13238, 13237, 5028, 13235, 5026, 5025, 13232]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row15 : Fin 64 → ℕ :=
  ![14016, 14050, 14049, 14019, 5860, 5830, 5829, 5863,
    14056, 14026, 14025, 14059, 5836, 5870, 5869, 5839,
    14047, 14077, 14078, 14044, 5883, 5849, 5850, 5880,
    14071, 14037, 14038, 14068, 5843, 5873, 5874, 5840,
    5856, 5826, 5825, 5859, 14020, 14054, 14053, 14023,
    5832, 5866, 5865, 5835, 14060, 14030, 14029, 14063,
    5887, 5853, 5854, 5884, 14043, 14073, 14074, 14040,
    5847, 5877, 5878, 5844, 14067, 14033, 14034, 14064]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row16 : Fin 64 → ℕ :=
  ![14080, 5906, 5905, 14083, 5908, 14086, 14085, 5911,
    14104, 5898, 5897, 14107, 5900, 14110, 14109, 5903,
    14127, 5949, 5950, 14124, 5947, 14121, 14122, 5944,
    14135, 5925, 5926, 14132, 5923, 14129, 14130, 5920,
    5904, 14082, 14081, 5907, 14084, 5910, 5909, 14087,
    5896, 14106, 14105, 5899, 14108, 5902, 5901, 14111,
    5951, 14125, 14126, 5948, 14123, 5945, 5946, 14120,
    5927, 14133, 14134, 5924, 14131, 5921, 5922, 14128]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row17 : Fin 64 → ℕ :=
  ![13888, 5714, 5713, 13891, 13908, 5702, 5701, 13911,
    5720, 13898, 13897, 5723, 5708, 13918, 13917, 5711,
    13935, 5757, 5758, 13932, 13947, 5737, 5738, 13944,
    5751, 13925, 13926, 5748, 5731, 13937, 13938, 5728,
    5712, 13890, 13889, 5715, 5700, 13910, 13909, 5703,
    13896, 5722, 5721, 13899, 13916, 5710, 5709, 13919,
    5759, 13933, 13934, 5756, 5739, 13945, 13946, 5736,
    13927, 5749, 5750, 13924, 13939, 5729, 5730, 13936]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row18 : Fin 64 → ℕ :=
  ![13952, 13986, 13985, 13955, 13988, 13958, 13957, 13991,
    5800, 5770, 5769, 5803, 5772, 5806, 5805, 5775,
    13983, 14013, 14014, 13980, 14011, 13977, 13978, 14008,
    5815, 5781, 5782, 5812, 5779, 5809, 5810, 5776,
    5792, 5762, 5761, 5795, 5764, 5798, 5797, 5767,
    13960, 13994, 13993, 13963, 13996, 13966, 13965, 13999,
    5823, 5789, 5790, 5820, 5787, 5817, 5818, 5784,
    13975, 14005, 14006, 13972, 14003, 13969, 13970, 14000]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row19 : Fin 64 → ℕ :=
  ![12416, 4286, 12475, 4229, 12477, 4227, 12422, 4280,
    4279, 12425, 4236, 12466, 4234, 12468, 4273, 12431,
    4287, 12417, 4228, 12474, 4226, 12476, 4281, 12423,
    12424, 4278, 12467, 4237, 12469, 4235, 12430, 4272,
    12463, 4241, 12436, 4266, 12434, 4268, 12457, 4247,
    4248, 12454, 4259, 12445, 4261, 12443, 4254, 12448,
    4240, 12462, 4267, 12437, 4269, 12435, 4246, 12456,
    12455, 4249, 12444, 4258, 12442, 4260, 12449, 4255]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row20 : Fin 64 → ℕ :=
  ![12352, 12376, 12370, 12362, 12372, 12364, 12358, 12382,
    12369, 12361, 12355, 12379, 12357, 12381, 12375, 12367,
    4208, 4200, 4194, 4218, 4196, 4220, 4214, 4206,
    4193, 4217, 4211, 4203, 4213, 4205, 4199, 4223,
    12399, 12407, 12413, 12389, 12411, 12387, 12393, 12401,
    12414, 12390, 12396, 12404, 12394, 12402, 12408, 12384,
    4191, 4167, 4173, 4181, 4171, 4179, 4185, 4161,
    4174, 4182, 4188, 4164, 4186, 4162, 4168, 4176]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row21 : Fin 64 → ℕ :=
  ![4736, 4770, 4769, 4739, 4772, 4742, 4741, 4775,
    12968, 12938, 12937, 12971, 12940, 12974, 12973, 12943,
    4767, 4797, 4798, 4764, 4795, 4761, 4762, 4792,
    12983, 12949, 12950, 12980, 12947, 12977, 12978, 12944,
    4768, 4738, 4737, 4771, 4740, 4774, 4773, 4743,
    12936, 12970, 12969, 12939, 12972, 12942, 12941, 12975,
    4799, 4765, 4766, 4796, 4763, 4793, 4794, 4760,
    12951, 12981, 12982, 12948, 12979, 12945, 12946, 12976]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row22 : Fin 64 → ℕ :=
  ![4672, 12898, 12897, 4675, 4708, 12870, 12869, 4711,
    12904, 4682, 4681, 12907, 12876, 4718, 4717, 12879,
    4704, 12866, 12865, 4707, 4676, 12902, 12901, 4679,
    12872, 4714, 4713, 12875, 12908, 4686, 4685, 12911,
    4703, 12925, 12926, 4700, 4731, 12889, 12890, 4728,
    12919, 4693, 4694, 12916, 12883, 4721, 4722, 12880,
    4735, 12893, 12894, 4732, 4699, 12921, 12922, 4696,
    12887, 4725, 4726, 12884, 12915, 4689, 4690, 12912]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row23 : Fin 64 → ℕ :=
  ![4608, 12834, 12833, 4611, 12836, 4614, 4613, 12839,
    4648, 12810, 12809, 4651, 12812, 4654, 4653, 12815,
    4640, 12802, 12801, 4643, 12804, 4646, 4645, 12807,
    4616, 12842, 12841, 4619, 12844, 4622, 4621, 12847,
    4639, 12861, 12862, 4636, 12859, 4633, 4634, 12856,
    4663, 12821, 12822, 4660, 12819, 4657, 4658, 12816,
    4671, 12829, 12830, 4668, 12827, 4665, 4666, 12824,
    4631, 12853, 12854, 4628, 12851, 4625, 4626, 12848]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row24 : Fin 64 → ℕ :=
  ![4544, 4578, 4577, 4547, 12772, 12742, 12741, 12775,
    4584, 4554, 4553, 4587, 12748, 12782, 12781, 12751,
    4575, 4605, 4606, 4572, 12795, 12761, 12762, 12792,
    4599, 4565, 4566, 4596, 12755, 12785, 12786, 12752,
    4576, 4546, 4545, 4579, 12740, 12774, 12773, 12743,
    4552, 4586, 4585, 4555, 12780, 12750, 12749, 12783,
    4607, 4573, 4574, 4604, 12763, 12793, 12794, 12760,
    4567, 4597, 4598, 4564, 12787, 12753, 12754, 12784]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row25 : Fin 64 → ℕ :=
  ![13376, 13410, 13409, 13379, 5220, 5190, 5189, 5223,
    13416, 13386, 13385, 13419, 5196, 5230, 5229, 5199,
    5216, 5186, 5185, 5219, 13380, 13414, 13413, 13383,
    5192, 5226, 5225, 5195, 13420, 13390, 13389, 13423,
    5215, 5245, 5246, 5212, 13435, 13401, 13402, 13432,
    5239, 5205, 5206, 5236, 13395, 13425, 13426, 13392,
    13439, 13405, 13406, 13436, 5211, 5241, 5242, 5208,
    13399, 13429, 13430, 13396, 5235, 5201, 5202, 5232]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row26 : Fin 64 → ℕ :=
  ![13440, 5282, 5281, 13443, 5284, 13446, 13445, 5287,
    13480, 5258, 5257, 13483, 5260, 13486, 13485, 5263,
    5279, 13501, 13502, 5276, 13499, 5273, 5274, 13496,
    5303, 13461, 13462, 5300, 13459, 5297, 5298, 13456,
    5280, 13442, 13441, 5283, 13444, 5286, 5285, 13447,
    5256, 13482, 13481, 5259, 13484, 5262, 5261, 13487,
    13503, 5277, 5278, 13500, 5275, 13497, 13498, 5272,
    13463, 5301, 5302, 13460, 5299, 13457, 13458, 5296]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row27 : Fin 64 → ℕ :=
  ![13248, 5090, 5089, 13251, 13284, 5062, 5061, 13287,
    5096, 13258, 13257, 5099, 5068, 13294, 13293, 5071,
    5087, 13309, 13310, 5084, 5115, 13273, 13274, 5112,
    13303, 5077, 5078, 13300, 13267, 5105, 5106, 13264,
    5088, 13250, 13249, 5091, 5060, 13286, 13285, 5063,
    13256, 5098, 5097, 13259, 13292, 5070, 5069, 13295,
    13311, 5085, 5086, 13308, 13275, 5113, 5114, 13272,
    5079, 13301, 13302, 5076, 5107, 13265, 13266, 5104]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row28 : Fin 64 → ℕ :=
  ![13312, 13346, 13345, 13315, 13348, 13318, 13317, 13351,
    5160, 5130, 5129, 5163, 5132, 5166, 5165, 5135,
    5152, 5122, 5121, 5155, 5124, 5158, 5157, 5127,
    13320, 13354, 13353, 13323, 13356, 13326, 13325, 13359,
    5151, 5181, 5182, 5148, 5179, 5145, 5146, 5176,
    13367, 13333, 13334, 13364, 13331, 13361, 13362, 13328,
    13375, 13341, 13342, 13372, 13339, 13369, 13370, 13336,
    5143, 5173, 5174, 5140, 5171, 5137, 5138, 5168]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row29 : Fin 64 → ℕ :=
  ![5952, 5953, 14161, 14160, 14206, 14207, 5999, 5998,
    5985, 5984, 14192, 14193, 14175, 14174, 5966, 5967,
    14147, 14146, 5970, 5971, 6013, 6012, 14188, 14189,
    14178, 14179, 6003, 6002, 5980, 5981, 14157, 14156,
    5961, 5960, 14168, 14169, 14199, 14198, 5990, 5991,
    5992, 5993, 14201, 14200, 14166, 14167, 5959, 5958,
    14154, 14155, 5979, 5978, 6004, 6005, 14181, 14180,
    14187, 14186, 6010, 6011, 5973, 5972, 14148, 14149]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row30 : Fin 64 → ℕ :=
  ![6016, 14248, 14242, 6026, 14244, 6028, 6022, 14254,
    14241, 6025, 6019, 14251, 6021, 14253, 14247, 6031,
    14256, 6040, 6034, 14266, 6036, 14268, 14262, 6046,
    6033, 14265, 14259, 6043, 14261, 6045, 6039, 14271,
    6048, 14216, 14210, 6058, 14212, 6060, 6054, 14222,
    14209, 6057, 6051, 14219, 6053, 14221, 14215, 6063,
    14224, 6072, 6066, 14234, 6068, 14236, 14230, 6078,
    6065, 14233, 14227, 6075, 14229, 6077, 6071, 14239]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row31 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6728, 14922, 14921, 6731,
    6724, 14918, 14917, 6727, 0, 0, 0, 0,
    0, 0, 0, 0, 14936, 6746, 6745, 14939,
    14932, 6742, 6741, 14935, 0, 0, 0, 0,
    0, 0, 0, 0, 6760, 14954, 14953, 6763,
    6756, 14950, 14949, 6759, 0, 0, 0, 0,
    0, 0, 0, 0, 14968, 6778, 6777, 14971,
    14964, 6774, 6773, 14967, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row32 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6728, 14922, 14921, 6731,
    6724, 14918, 14917, 6727, 0, 0, 0, 0,
    0, 0, 0, 0, 14936, 6746, 6745, 14939,
    14932, 6742, 6741, 14935, 0, 0, 0, 0,
    0, 0, 0, 0, 6760, 14954, 14953, 6763,
    6756, 14950, 14949, 6759, 0, 0, 0, 0,
    0, 0, 0, 0, 14968, 6778, 6777, 14971,
    14964, 6774, 6773, 14967, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row33 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 16104, 16073, 16074, 16107,
    16100, 16069, 16070, 16103, 0, 0, 0, 0,
    0, 0, 0, 0, 16119, 16086, 16085, 16116,
    16123, 16090, 16089, 16120, 0, 0, 0, 0,
    0, 0, 0, 0, 7880, 7913, 7914, 7883,
    7876, 7909, 7910, 7879, 0, 0, 0, 0,
    0, 0, 0, 0, 7895, 7926, 7925, 7892,
    7899, 7930, 7929, 7896, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row34 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 16104, 16073, 16074, 16107,
    16100, 16069, 16070, 16103, 0, 0, 0, 0,
    0, 0, 0, 0, 16119, 16086, 16085, 16116,
    16123, 16090, 16089, 16120, 0, 0, 0, 0,
    0, 0, 0, 0, 7880, 7913, 7914, 7883,
    7876, 7909, 7910, 7879, 0, 0, 0, 0,
    0, 0, 0, 0, 7895, 7926, 7925, 7892,
    7899, 7930, 7929, 7896, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row35 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14568, 14538, 14537, 14571,
    14564, 14534, 14533, 14567, 0, 0, 0, 0,
    0, 0, 0, 0, 6391, 6357, 6358, 6388,
    6395, 6361, 6362, 6392, 0, 0, 0, 0,
    0, 0, 0, 0, 14536, 14570, 14569, 14539,
    14532, 14566, 14565, 14535, 0, 0, 0, 0,
    0, 0, 0, 0, 6359, 6389, 6390, 6356,
    6363, 6393, 6394, 6360, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row36 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14568, 14538, 14537, 14571,
    14564, 14534, 14533, 14567, 0, 0, 0, 0,
    0, 0, 0, 0, 6391, 6357, 6358, 6388,
    6395, 6361, 6362, 6392, 0, 0, 0, 0,
    0, 0, 0, 0, 14536, 14570, 14569, 14539,
    14532, 14566, 14565, 14535, 0, 0, 0, 0,
    0, 0, 0, 0, 6359, 6389, 6390, 6356,
    6363, 6393, 6394, 6360, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row37 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15432, 15434, 15433, 15435,
    15428, 15430, 15429, 15431, 0, 0, 0, 0,
    0, 0, 0, 0, 7256, 7258, 7257, 7259,
    7252, 7254, 7253, 7255, 0, 0, 0, 0,
    0, 0, 0, 0, 15464, 15466, 15465, 15467,
    15460, 15462, 15461, 15463, 0, 0, 0, 0,
    0, 0, 0, 0, 7288, 7290, 7289, 7291,
    7284, 7286, 7285, 7287, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row38 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15432, 15434, 15433, 15435,
    15428, 15430, 15429, 15431, 0, 0, 0, 0,
    0, 0, 0, 0, 7256, 7258, 7257, 7259,
    7252, 7254, 7253, 7255, 0, 0, 0, 0,
    0, 0, 0, 0, 15464, 15466, 15465, 15467,
    15460, 15462, 15461, 15463, 0, 0, 0, 0,
    0, 0, 0, 0, 7288, 7290, 7289, 7291,
    7284, 7286, 7285, 7287, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row39 : Fin 64 → ℕ :=
  ![0, 15714, 15713, 0, 0, 15686, 15685, 0,
    0, 15690, 15689, 0, 0, 15726, 15725, 0,
    0, 7490, 7489, 0, 0, 7526, 7525, 0,
    0, 7530, 7529, 0, 0, 7502, 7501, 0,
    0, 7549, 7550, 0, 0, 7513, 7514, 0,
    0, 7509, 7510, 0, 0, 7537, 7538, 0,
    0, 15709, 15710, 0, 0, 15737, 15738, 0,
    0, 15733, 15734, 0, 0, 15697, 15698, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row40 : Fin 64 → ℕ :=
  ![0, 15714, 15713, 0, 0, 15686, 15685, 0,
    0, 15690, 15689, 0, 0, 15726, 15725, 0,
    0, 7490, 7489, 0, 0, 7526, 7525, 0,
    0, 7530, 7529, 0, 0, 7502, 7501, 0,
    0, 7549, 7550, 0, 0, 7513, 7514, 0,
    0, 7509, 7510, 0, 0, 7537, 7538, 0,
    0, 15709, 15710, 0, 0, 15737, 15738, 0,
    0, 15733, 15734, 0, 0, 15697, 15698, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row41 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6088, 14282, 14281, 6091,
    6084, 14278, 14277, 6087, 0, 0, 0, 0,
    0, 0, 0, 0, 14296, 6106, 6105, 14299,
    14292, 6102, 6101, 14295, 0, 0, 0, 0,
    0, 0, 0, 0, 6120, 14314, 14313, 6123,
    6116, 14310, 14309, 6119, 0, 0, 0, 0,
    0, 0, 0, 0, 14328, 6138, 6137, 14331,
    14324, 6134, 6133, 14327, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row42 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6088, 14282, 14281, 6091,
    6084, 14278, 14277, 6087, 0, 0, 0, 0,
    0, 0, 0, 0, 14296, 6106, 6105, 14299,
    14292, 6102, 6101, 14295, 0, 0, 0, 0,
    0, 0, 0, 0, 6120, 14314, 14313, 6123,
    6116, 14310, 14309, 6119, 0, 0, 0, 0,
    0, 0, 0, 0, 14328, 6138, 6137, 14331,
    14324, 6134, 6133, 14327, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row43 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15816, 15818, 15817, 15819,
    15812, 15814, 15813, 15815, 0, 0, 0, 0,
    0, 0, 0, 0, 15832, 15834, 15833, 15835,
    15828, 15830, 15829, 15831, 0, 0, 0, 0,
    0, 0, 0, 0, 7656, 7658, 7657, 7659,
    7652, 7654, 7653, 7655, 0, 0, 0, 0,
    0, 0, 0, 0, 7672, 7674, 7673, 7675,
    7668, 7670, 7669, 7671, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row44 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15816, 15818, 15817, 15819,
    15812, 15814, 15813, 15815, 0, 0, 0, 0,
    0, 0, 0, 0, 15832, 15834, 15833, 15835,
    15828, 15830, 15829, 15831, 0, 0, 0, 0,
    0, 0, 0, 0, 7656, 7658, 7657, 7659,
    7652, 7654, 7653, 7655, 0, 0, 0, 0,
    0, 0, 0, 0, 7672, 7674, 7673, 7675,
    7668, 7670, 7669, 7671, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row45 : Fin 64 → ℕ :=
  ![0, 6994, 6993, 0, 0, 6986, 6985, 0,
    0, 6982, 6981, 0, 0, 7006, 7005, 0,
    0, 6978, 6977, 0, 0, 7002, 7001, 0,
    0, 6998, 6997, 0, 0, 6990, 6989, 0,
    0, 7037, 7038, 0, 0, 7013, 7014, 0,
    0, 7017, 7018, 0, 0, 7025, 7026, 0,
    0, 7021, 7022, 0, 0, 7029, 7030, 0,
    0, 7033, 7034, 0, 0, 7009, 7010, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row46 : Fin 64 → ℕ :=
  ![0, 6994, 6993, 0, 0, 6986, 6985, 0,
    0, 6982, 6981, 0, 0, 7006, 7005, 0,
    0, 6978, 6977, 0, 0, 7002, 7001, 0,
    0, 6998, 6997, 0, 0, 6990, 6989, 0,
    0, 7037, 7038, 0, 0, 7013, 7014, 0,
    0, 7017, 7018, 0, 0, 7025, 7026, 0,
    0, 7021, 7022, 0, 0, 7029, 7030, 0,
    0, 7033, 7034, 0, 0, 7009, 7010, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row47 : Fin 64 → ℕ :=
  ![0, 15330, 15329, 0, 0, 7114, 7113, 0,
    0, 7110, 7109, 0, 0, 15342, 15341, 0,
    0, 15357, 15358, 0, 0, 7125, 7126, 0,
    0, 7129, 7130, 0, 0, 15345, 15346, 0,
    0, 15298, 15297, 0, 0, 7146, 7145, 0,
    0, 7142, 7141, 0, 0, 15310, 15309, 0,
    0, 15325, 15326, 0, 0, 7157, 7158, 0,
    0, 7161, 7162, 0, 0, 15313, 15314, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row48 : Fin 64 → ℕ :=
  ![0, 15330, 15329, 0, 0, 7114, 7113, 0,
    0, 7110, 7109, 0, 0, 15342, 15341, 0,
    0, 15357, 15358, 0, 0, 7125, 7126, 0,
    0, 7129, 7130, 0, 0, 15345, 15346, 0,
    0, 15298, 15297, 0, 0, 7146, 7145, 0,
    0, 7142, 7141, 0, 0, 15310, 15309, 0,
    0, 15325, 15326, 0, 0, 7157, 7158, 0,
    0, 7161, 7162, 0, 0, 15313, 15314, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row49 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14664, 14666, 14665, 14667,
    14660, 14662, 14661, 14663, 0, 0, 0, 0,
    0, 0, 0, 0, 6488, 6490, 6489, 6491,
    6484, 6486, 6485, 6487, 0, 0, 0, 0,
    0, 0, 0, 0, 14696, 14698, 14697, 14699,
    14692, 14694, 14693, 14695, 0, 0, 0, 0,
    0, 0, 0, 0, 6520, 6522, 6521, 6523,
    6516, 6518, 6517, 6519, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row50 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14664, 14666, 14665, 14667,
    14660, 14662, 14661, 14663, 0, 0, 0, 0,
    0, 0, 0, 0, 6488, 6490, 6489, 6491,
    6484, 6486, 6485, 6487, 0, 0, 0, 0,
    0, 0, 0, 0, 14696, 14698, 14697, 14699,
    14692, 14694, 14693, 14695, 0, 0, 0, 0,
    0, 0, 0, 0, 6520, 6522, 6521, 6523,
    6516, 6518, 6517, 6519, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row51 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 8008, 16202, 16201, 8011,
    8004, 16198, 16197, 8007, 0, 0, 0, 0,
    0, 0, 0, 0, 8024, 16218, 16217, 8027,
    8020, 16214, 16213, 8023, 0, 0, 0, 0,
    0, 0, 0, 0, 16232, 8042, 8041, 16235,
    16228, 8038, 8037, 16231, 0, 0, 0, 0,
    0, 0, 0, 0, 16248, 8058, 8057, 16251,
    16244, 8054, 8053, 16247, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row52 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 8008, 16202, 16201, 8011,
    8004, 16198, 16197, 8007, 0, 0, 0, 0,
    0, 0, 0, 0, 8024, 16218, 16217, 8027,
    8020, 16214, 16213, 8023, 0, 0, 0, 0,
    0, 0, 0, 0, 16232, 8042, 8041, 16235,
    16228, 8038, 8037, 16231, 0, 0, 0, 0,
    0, 0, 0, 0, 16248, 8058, 8057, 16251,
    16244, 8054, 8053, 16247, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row53 : Fin 64 → ℕ :=
  ![0, 6610, 6609, 0, 0, 14790, 14789, 0,
    0, 14794, 14793, 0, 0, 6622, 6621, 0,
    0, 14845, 14846, 0, 0, 6633, 6634, 0,
    0, 6629, 6630, 0, 0, 14833, 14834, 0,
    0, 14786, 14785, 0, 0, 6614, 6613, 0,
    0, 6618, 6617, 0, 0, 14798, 14797, 0,
    0, 6637, 6638, 0, 0, 14841, 14842, 0,
    0, 14837, 14838, 0, 0, 6625, 6626, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row54 : Fin 64 → ℕ :=
  ![0, 6610, 6609, 0, 0, 14790, 14789, 0,
    0, 14794, 14793, 0, 0, 6622, 6621, 0,
    0, 14845, 14846, 0, 0, 6633, 6634, 0,
    0, 6629, 6630, 0, 0, 14833, 14834, 0,
    0, 14786, 14785, 0, 0, 6614, 6613, 0,
    0, 6618, 6617, 0, 0, 14798, 14797, 0,
    0, 6637, 6638, 0, 0, 14841, 14842, 0,
    0, 14837, 14838, 0, 0, 6625, 6626, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row55 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15048, 15050, 15049, 15051,
    15044, 15046, 15045, 15047, 0, 0, 0, 0,
    0, 0, 0, 0, 15064, 15066, 15065, 15067,
    15060, 15062, 15061, 15063, 0, 0, 0, 0,
    0, 0, 0, 0, 6888, 6890, 6889, 6891,
    6884, 6886, 6885, 6887, 0, 0, 0, 0,
    0, 0, 0, 0, 6904, 6906, 6905, 6907,
    6900, 6902, 6901, 6903, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row56 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15048, 15050, 15049, 15051,
    15044, 15046, 15045, 15047, 0, 0, 0, 0,
    0, 0, 0, 0, 15064, 15066, 15065, 15067,
    15060, 15062, 15061, 15063, 0, 0, 0, 0,
    0, 0, 0, 0, 6888, 6890, 6889, 6891,
    6884, 6886, 6885, 6887, 0, 0, 0, 0,
    0, 0, 0, 0, 6904, 6906, 6905, 6907,
    6900, 6902, 6901, 6903, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row57 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7784, 15946, 15945, 7787,
    7780, 15942, 15941, 7783, 0, 0, 0, 0,
    0, 0, 0, 0, 15991, 7765, 7766, 15988,
    15995, 7769, 7770, 15992, 0, 0, 0, 0,
    0, 0, 0, 0, 7752, 15978, 15977, 7755,
    7748, 15974, 15973, 7751, 0, 0, 0, 0,
    0, 0, 0, 0, 15959, 7797, 7798, 15956,
    15963, 7801, 7802, 15960, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row58 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7784, 15946, 15945, 7787,
    7780, 15942, 15941, 7783, 0, 0, 0, 0,
    0, 0, 0, 0, 15991, 7765, 7766, 15988,
    15995, 7769, 7770, 15992, 0, 0, 0, 0,
    0, 0, 0, 0, 7752, 15978, 15977, 7755,
    7748, 15974, 15973, 7751, 0, 0, 0, 0,
    0, 0, 0, 0, 15959, 7797, 7798, 15956,
    15963, 7801, 7802, 15960, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row59 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6248, 14409, 14410, 6251,
    6244, 14405, 14406, 6247, 0, 0, 0, 0,
    0, 0, 0, 0, 6263, 14422, 14421, 6260,
    6267, 14426, 14425, 6264, 0, 0, 0, 0,
    0, 0, 0, 0, 14408, 6249, 6250, 14411,
    14404, 6245, 6246, 14407, 0, 0, 0, 0,
    0, 0, 0, 0, 14423, 6262, 6261, 14420,
    14427, 6266, 6265, 14424, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row60 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6248, 14409, 14410, 6251,
    6244, 14405, 14406, 6247, 0, 0, 0, 0,
    0, 0, 0, 0, 6263, 14422, 14421, 6260,
    6267, 14426, 14425, 6264, 0, 0, 0, 0,
    0, 0, 0, 0, 14408, 6249, 6250, 14411,
    14404, 6245, 6246, 14407, 0, 0, 0, 0,
    0, 0, 0, 0, 14423, 6262, 6261, 14420,
    14427, 6266, 6265, 14424, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row61 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7368, 15562, 15561, 7371,
    7364, 15558, 15557, 7367, 0, 0, 0, 0,
    0, 0, 0, 0, 7384, 15578, 15577, 7387,
    7380, 15574, 15573, 7383, 0, 0, 0, 0,
    0, 0, 0, 0, 15592, 7402, 7401, 15595,
    15588, 7398, 7397, 15591, 0, 0, 0, 0,
    0, 0, 0, 0, 15608, 7418, 7417, 15611,
    15604, 7414, 7413, 15607, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord1Row62 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7368, 15562, 15561, 7371,
    7364, 15558, 15557, 7367, 0, 0, 0, 0,
    0, 0, 0, 0, 7384, 15578, 15577, 7387,
    7380, 15574, 15573, 7383, 0, 0, 0, 0,
    0, 0, 0, 0, 15592, 7402, 7401, 15595,
    15588, 7398, 7397, 15591, 0, 0, 0, 0,
    0, 0, 0, 0, 15608, 7418, 7417, 15611,
    15604, 7414, 7413, 15607, 0, 0, 0, 0]

/-- Literal candidate octad target addresses, with the target central phase retained. -/
def generatedFourthMonomialShortOctadTargets1 : Fin 63 → Fin 64 → ℕ :=
  ![
    generatedFourthMonomialOctadWord1Row0,
    generatedFourthMonomialOctadWord1Row1,
    generatedFourthMonomialOctadWord1Row2,
    generatedFourthMonomialOctadWord1Row3,
    generatedFourthMonomialOctadWord1Row4,
    generatedFourthMonomialOctadWord1Row5,
    generatedFourthMonomialOctadWord1Row6,
    generatedFourthMonomialOctadWord1Row7,
    generatedFourthMonomialOctadWord1Row8,
    generatedFourthMonomialOctadWord1Row9,
    generatedFourthMonomialOctadWord1Row10,
    generatedFourthMonomialOctadWord1Row11,
    generatedFourthMonomialOctadWord1Row12,
    generatedFourthMonomialOctadWord1Row13,
    generatedFourthMonomialOctadWord1Row14,
    generatedFourthMonomialOctadWord1Row15,
    generatedFourthMonomialOctadWord1Row16,
    generatedFourthMonomialOctadWord1Row17,
    generatedFourthMonomialOctadWord1Row18,
    generatedFourthMonomialOctadWord1Row19,
    generatedFourthMonomialOctadWord1Row20,
    generatedFourthMonomialOctadWord1Row21,
    generatedFourthMonomialOctadWord1Row22,
    generatedFourthMonomialOctadWord1Row23,
    generatedFourthMonomialOctadWord1Row24,
    generatedFourthMonomialOctadWord1Row25,
    generatedFourthMonomialOctadWord1Row26,
    generatedFourthMonomialOctadWord1Row27,
    generatedFourthMonomialOctadWord1Row28,
    generatedFourthMonomialOctadWord1Row29,
    generatedFourthMonomialOctadWord1Row30,
    generatedFourthMonomialOctadWord1Row31,
    generatedFourthMonomialOctadWord1Row32,
    generatedFourthMonomialOctadWord1Row33,
    generatedFourthMonomialOctadWord1Row34,
    generatedFourthMonomialOctadWord1Row35,
    generatedFourthMonomialOctadWord1Row36,
    generatedFourthMonomialOctadWord1Row37,
    generatedFourthMonomialOctadWord1Row38,
    generatedFourthMonomialOctadWord1Row39,
    generatedFourthMonomialOctadWord1Row40,
    generatedFourthMonomialOctadWord1Row41,
    generatedFourthMonomialOctadWord1Row42,
    generatedFourthMonomialOctadWord1Row43,
    generatedFourthMonomialOctadWord1Row44,
    generatedFourthMonomialOctadWord1Row45,
    generatedFourthMonomialOctadWord1Row46,
    generatedFourthMonomialOctadWord1Row47,
    generatedFourthMonomialOctadWord1Row48,
    generatedFourthMonomialOctadWord1Row49,
    generatedFourthMonomialOctadWord1Row50,
    generatedFourthMonomialOctadWord1Row51,
    generatedFourthMonomialOctadWord1Row52,
    generatedFourthMonomialOctadWord1Row53,
    generatedFourthMonomialOctadWord1Row54,
    generatedFourthMonomialOctadWord1Row55,
    generatedFourthMonomialOctadWord1Row56,
    generatedFourthMonomialOctadWord1Row57,
    generatedFourthMonomialOctadWord1Row58,
    generatedFourthMonomialOctadWord1Row59,
    generatedFourthMonomialOctadWord1Row60,
    generatedFourthMonomialOctadWord1Row61,
    generatedFourthMonomialOctadWord1Row62
  ]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row0 : Fin 24 → ℕ :=
  ![0, 146, 148, 144, 0, 0, 0, 0,
    0, 0, 0, 0, 582, 8870, 8822, 726,
    1062, 9158, 9302, 1014, 9014, 918, 774, 9062]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row1 : Fin 24 → ℕ :=
  ![0, 0, 98, 48, 0, 0, 0, 0,
    0, 0, 0, 0, 578, 8866, 8818, 722,
    1058, 9154, 9298, 1010, 9010, 914, 770, 9058]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 96, 0, 0, 0, 0,
    0, 0, 0, 0, 580, 8868, 8820, 724,
    1060, 9156, 9300, 1012, 9012, 916, 772, 9060]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 576, 8864, 8816, 720,
    1056, 9152, 9296, 1008, 9008, 912, 768, 9056]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 296, 248, 344,
    8728, 440, 488, 8584, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 298, 348,
    8732, 444, 492, 8588, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 346,
    8730, 442, 490, 8586, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    8734, 446, 494, 8590, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 8738, 8740, 544, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 498, 8640, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 8688, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 8888, 8840, 744,
    1080, 9176, 9320, 1032, 9032, 936, 792, 9080]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 698, 8940,
    9276, 988, 1132, 9228, 844, 9132, 8988, 892]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 8938,
    9274, 986, 1130, 9226, 842, 9130, 8986, 890]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1086, 9182, 9326, 1038, 9038, 942, 798, 9086]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 9288, 9340, 1098, 9282, 1094, 1088, 9284]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1144, 9240, 994, 9190, 9184, 996]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 9338, 1138, 9334, 9328, 1140]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 9234, 1046, 1040, 9236]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9138, 9040, 898]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 944, 9140]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 9088]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign0Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row0 : Fin 24 → ℕ :=
  ![0, 147, 149, 145, 0, 0, 0, 0,
    0, 0, 0, 0, 583, 8871, 8823, 727,
    1063, 9159, 9303, 1015, 9015, 919, 775, 9063]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row1 : Fin 24 → ℕ :=
  ![0, 0, 99, 49, 0, 0, 0, 0,
    0, 0, 0, 0, 579, 8867, 8819, 723,
    1059, 9155, 9299, 1011, 9011, 915, 771, 9059]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 97, 0, 0, 0, 0,
    0, 0, 0, 0, 581, 8869, 8821, 725,
    1061, 9157, 9301, 1013, 9013, 917, 773, 9061]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 577, 8865, 8817, 721,
    1057, 9153, 9297, 1009, 9009, 913, 769, 9057]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 297, 249, 345,
    8729, 441, 489, 8585, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 299, 349,
    8733, 445, 493, 8589, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 347,
    8731, 443, 491, 8587, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    8735, 447, 495, 8591, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 8739, 8741, 545, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 499, 8641, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 8689, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 8889, 8841, 745,
    1081, 9177, 9321, 1033, 9033, 937, 793, 9081]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 699, 8941,
    9277, 989, 1133, 9229, 845, 9133, 8989, 893]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 8939,
    9275, 987, 1131, 9227, 843, 9131, 8987, 891]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    1087, 9183, 9327, 1039, 9039, 943, 799, 9087]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 9289, 9341, 1099, 9283, 1095, 1089, 9285]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1145, 9241, 995, 9191, 9185, 997]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 9339, 1139, 9335, 9329, 1141]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 9235, 1047, 1041, 9237]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9139, 9041, 899]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 945, 9141]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 9089]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord1Sign1Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- Literal candidate pair target addresses for both original preferred signs. -/
def generatedFourthMonomialShortPairTargets1 : Fin 2 → Fin 24 → Fin 24 → ℕ :=
  ![
    ![generatedFourthMonomialPairWord1Sign0Row0,
    generatedFourthMonomialPairWord1Sign0Row1,
    generatedFourthMonomialPairWord1Sign0Row2,
    generatedFourthMonomialPairWord1Sign0Row3,
    generatedFourthMonomialPairWord1Sign0Row4,
    generatedFourthMonomialPairWord1Sign0Row5,
      generatedFourthMonomialPairWord1Sign0Row6,
    generatedFourthMonomialPairWord1Sign0Row7,
    generatedFourthMonomialPairWord1Sign0Row8,
    generatedFourthMonomialPairWord1Sign0Row9,
    generatedFourthMonomialPairWord1Sign0Row10,
    generatedFourthMonomialPairWord1Sign0Row11,
      generatedFourthMonomialPairWord1Sign0Row12,
    generatedFourthMonomialPairWord1Sign0Row13,
    generatedFourthMonomialPairWord1Sign0Row14,
    generatedFourthMonomialPairWord1Sign0Row15,
    generatedFourthMonomialPairWord1Sign0Row16,
    generatedFourthMonomialPairWord1Sign0Row17,
      generatedFourthMonomialPairWord1Sign0Row18,
    generatedFourthMonomialPairWord1Sign0Row19,
    generatedFourthMonomialPairWord1Sign0Row20,
    generatedFourthMonomialPairWord1Sign0Row21,
    generatedFourthMonomialPairWord1Sign0Row22,
    generatedFourthMonomialPairWord1Sign0Row23],
    ![generatedFourthMonomialPairWord1Sign1Row0,
    generatedFourthMonomialPairWord1Sign1Row1,
    generatedFourthMonomialPairWord1Sign1Row2,
    generatedFourthMonomialPairWord1Sign1Row3,
    generatedFourthMonomialPairWord1Sign1Row4,
    generatedFourthMonomialPairWord1Sign1Row5,
      generatedFourthMonomialPairWord1Sign1Row6,
    generatedFourthMonomialPairWord1Sign1Row7,
    generatedFourthMonomialPairWord1Sign1Row8,
    generatedFourthMonomialPairWord1Sign1Row9,
    generatedFourthMonomialPairWord1Sign1Row10,
    generatedFourthMonomialPairWord1Sign1Row11,
      generatedFourthMonomialPairWord1Sign1Row12,
    generatedFourthMonomialPairWord1Sign1Row13,
    generatedFourthMonomialPairWord1Sign1Row14,
    generatedFourthMonomialPairWord1Sign1Row15,
    generatedFourthMonomialPairWord1Sign1Row16,
    generatedFourthMonomialPairWord1Sign1Row17,
      generatedFourthMonomialPairWord1Sign1Row18,
    generatedFourthMonomialPairWord1Sign1Row19,
    generatedFourthMonomialPairWord1Sign1Row20,
    generatedFourthMonomialPairWord1Sign1Row21,
    generatedFourthMonomialPairWord1Sign1Row22,
    generatedFourthMonomialPairWord1Sign1Row23]
  ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
