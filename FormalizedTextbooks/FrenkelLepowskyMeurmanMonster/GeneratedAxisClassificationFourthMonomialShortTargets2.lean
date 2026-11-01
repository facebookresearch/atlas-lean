/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation

/-! Candidate full signed short-image addresses for original corrected monomial word 2.
They assert no correctness until checked against the actual Q images and numerators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000
-- Each candidate row has at most64 literal addresses; row names bound vector elaboration.

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row0 : Fin 64 → ℕ :=
  ![4096, 4097, 4128, 4129, 4104, 4105, 4136, 4137,
    4100, 4101, 4132, 4133, 4108, 4109, 4140, 4141,
    4112, 4113, 4144, 4145, 4120, 4121, 4152, 4153,
    4116, 4117, 4148, 4149, 4124, 4125, 4156, 4157,
    4098, 4099, 4130, 4131, 4106, 4107, 4138, 4139,
    4102, 4103, 4134, 4135, 4110, 4111, 4142, 4143,
    4114, 4115, 4146, 4147, 4122, 4123, 4154, 4155,
    4118, 4119, 4150, 4151, 4126, 4127, 4158, 4159]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row1 : Fin 64 → ℕ :=
  ![4800, 4862, 4859, 4805, 13055, 12993, 12996, 13050,
    13023, 13025, 13028, 13018, 4832, 4830, 4827, 4837,
    13047, 13001, 13004, 13042, 4808, 4854, 4851, 4813,
    4840, 4822, 4819, 4845, 13015, 13033, 13036, 13010,
    4847, 4817, 4820, 4842, 13008, 13038, 13035, 13013,
    13040, 13006, 13003, 13045, 4815, 4849, 4852, 4810,
    13016, 13030, 13027, 13021, 4839, 4825, 4828, 4834,
    4807, 4857, 4860, 4802, 13048, 12998, 12995, 13053]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row2 : Fin 64 → ℕ :=
  ![4864, 13059, 13062, 4869, 4866, 13057, 13060, 4871,
    4882, 13073, 13076, 4887, 4880, 13075, 13078, 4885,
    4874, 13065, 13068, 4879, 4872, 13067, 13070, 4877,
    4888, 13083, 13086, 4893, 4890, 13081, 13084, 4895,
    13117, 4926, 4923, 13112, 13119, 4924, 4921, 13114,
    13103, 4908, 4905, 13098, 13101, 4910, 4907, 13096,
    13111, 4916, 4913, 13106, 13109, 4918, 4915, 13104,
    13093, 4902, 4899, 13088, 13095, 4900, 4897, 13090]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row3 : Fin 64 → ℕ :=
  ![4288, 12486, 4290, 12484, 12483, 4293, 12481, 4295,
    4306, 12500, 4304, 12502, 12497, 4311, 12499, 4309,
    4298, 12492, 4296, 12494, 12489, 4303, 12491, 4301,
    4312, 12510, 4314, 12508, 12507, 4317, 12505, 4319,
    12541, 4347, 12543, 4345, 4350, 12536, 4348, 12538,
    12527, 4329, 12525, 4331, 4332, 12522, 4334, 12520,
    12535, 4337, 12533, 4339, 4340, 12530, 4342, 12528,
    12517, 4323, 12519, 4321, 4326, 12512, 4324, 12514]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row4 : Fin 64 → ℕ :=
  ![4352, 12553, 4392, 12577, 12556, 4357, 12580, 4397,
    4360, 12545, 4384, 12585, 12548, 4365, 12588, 4389,
    12568, 4369, 12592, 4409, 4372, 12573, 4412, 12597,
    12560, 4377, 12600, 4401, 4380, 12565, 4404, 12605,
    4362, 12547, 4386, 12587, 12550, 4367, 12590, 4391,
    4354, 12555, 4394, 12579, 12558, 4359, 12582, 4399,
    12562, 4379, 12602, 4403, 4382, 12567, 4406, 12607,
    12570, 4371, 12594, 4411, 4374, 12575, 4414, 12599]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row5 : Fin 64 → ℕ :=
  ![5568, 13765, 5630, 13819, 13769, 5580, 13815, 5618,
    5569, 13764, 5631, 13818, 13768, 5581, 13814, 5619,
    13777, 5588, 13807, 5610, 5592, 13789, 5606, 13795,
    13776, 5589, 13806, 5611, 5593, 13788, 5607, 13794,
    5571, 13766, 5629, 13816, 13770, 5583, 13812, 5617,
    5570, 13767, 5628, 13817, 13771, 5582, 13813, 5616,
    13778, 5591, 13804, 5609, 5595, 13790, 5605, 13792,
    13779, 5590, 13805, 5608, 5594, 13791, 5604, 13793]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row6 : Fin 64 → ℕ :=
  ![5632, 13829, 5668, 13857, 13830, 5635, 13858, 5671,
    5652, 13841, 5680, 13877, 13842, 5655, 13878, 5683,
    5644, 13833, 5672, 13869, 13834, 5647, 13870, 5675,
    5656, 13853, 5692, 13881, 13854, 5659, 13882, 5695,
    13883, 5694, 13855, 5658, 5693, 13880, 5657, 13852,
    13871, 5674, 13835, 5646, 5673, 13868, 5645, 13832,
    13879, 5682, 13843, 5654, 5681, 13876, 5653, 13840,
    13859, 5670, 13831, 5634, 5669, 13856, 5633, 13828]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row7 : Fin 64 → ℕ :=
  ![13632, 13636, 5472, 5476, 13640, 13644, 5480, 5484,
    5456, 5460, 13680, 13684, 5464, 5468, 13688, 13692,
    13695, 13691, 5471, 5467, 13687, 13683, 5463, 5459,
    5487, 5483, 13647, 13643, 5479, 5475, 13639, 13635,
    5442, 5446, 13666, 13670, 5450, 5454, 13674, 13678,
    13650, 13654, 5490, 5494, 13658, 13662, 5498, 5502,
    5501, 5497, 13661, 13657, 5493, 5489, 13653, 13649,
    13677, 13673, 5453, 5449, 13669, 13665, 5445, 5441]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row8 : Fin 64 → ℕ :=
  ![13696, 5509, 13755, 5566, 5510, 13699, 5565, 13752,
    13700, 5505, 13759, 5562, 5506, 13703, 5561, 13756,
    13708, 5513, 13751, 5554, 5514, 13711, 5553, 13748,
    13704, 5517, 13747, 5558, 5518, 13707, 5557, 13744,
    5524, 13713, 5551, 13738, 13714, 5527, 13737, 5548,
    5520, 13717, 5547, 13742, 13718, 5523, 13741, 5544,
    5528, 13725, 5539, 13734, 13726, 5531, 13733, 5536,
    5532, 13721, 5543, 13730, 13722, 5535, 13729, 5540]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row9 : Fin 64 → ℕ :=
  ![13504, 5317, 13563, 5374, 5318, 13507, 5373, 13560,
    13524, 5329, 13551, 5354, 5330, 13527, 5353, 13548,
    13516, 5321, 13559, 5362, 5322, 13519, 5361, 13556,
    13528, 5341, 13539, 5350, 5342, 13531, 5349, 13536,
    5348, 13537, 5343, 13530, 13538, 5351, 13529, 5340,
    5360, 13557, 5323, 13518, 13558, 5363, 13517, 5320,
    5352, 13549, 5331, 13526, 13550, 5355, 13525, 5328,
    5372, 13561, 5319, 13506, 13562, 5375, 13505, 5316]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row10 : Fin 64 → ℕ :=
  ![13568, 13601, 5408, 5377, 13602, 13571, 5378, 5411,
    5424, 5393, 13584, 13617, 5394, 5427, 13618, 13587,
    13599, 13630, 5439, 5406, 13629, 13596, 5405, 5436,
    5423, 5390, 13583, 13614, 5389, 5420, 13613, 13580,
    5416, 5385, 13576, 13609, 5386, 5419, 13610, 13579,
    13592, 13625, 5432, 5401, 13626, 13595, 5402, 5435,
    5431, 5398, 13591, 13622, 5397, 5428, 13621, 13588,
    13575, 13606, 5415, 5382, 13605, 13572, 5381, 5412]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row11 : Fin 64 → ℕ :=
  ![4160, 12357, 4219, 12414, 12358, 4163, 12413, 4216,
    4180, 12369, 4207, 12394, 12370, 4183, 12393, 4204,
    12388, 4193, 12383, 4186, 4194, 12391, 4185, 12380,
    12400, 4213, 12363, 4174, 4214, 12403, 4173, 12360,
    4172, 12361, 4215, 12402, 12362, 4175, 12401, 4212,
    4184, 12381, 4195, 12390, 12382, 4187, 12389, 4192,
    12392, 4205, 12371, 4182, 4206, 12395, 4181, 12368,
    12412, 4217, 12359, 4162, 4218, 12415, 4161, 12356]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row12 : Fin 64 → ℕ :=
  ![4224, 12421, 4228, 12417, 12422, 4227, 12418, 4231,
    4244, 12433, 4240, 12437, 12434, 4247, 12438, 4243,
    4236, 12425, 4232, 12429, 12426, 4239, 12430, 4235,
    4248, 12445, 4252, 12441, 12446, 4251, 12442, 4255,
    12475, 4286, 12479, 4282, 4285, 12472, 4281, 12476,
    12463, 4266, 12459, 4270, 4265, 12460, 4269, 12456,
    12471, 4274, 12467, 4278, 4273, 12468, 4277, 12464,
    12451, 4262, 12455, 4258, 4261, 12448, 4257, 12452]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row13 : Fin 64 → ℕ :=
  ![13376, 5187, 13410, 5217, 5190, 13381, 5220, 13415,
    13378, 5185, 13408, 5219, 5188, 13383, 5222, 13413,
    13386, 5193, 13416, 5227, 5196, 13391, 5230, 13421,
    13384, 5195, 13418, 5225, 5198, 13389, 5228, 13423,
    5245, 13438, 5215, 13404, 13435, 5240, 13401, 5210,
    5247, 13436, 5213, 13406, 13433, 5242, 13403, 5208,
    5239, 13428, 5205, 13398, 13425, 5234, 13395, 5200,
    5237, 13430, 5207, 13396, 13427, 5232, 13393, 5202]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row14 : Fin 64 → ℕ :=
  ![13440, 5260, 13495, 5307, 5257, 13445, 5310, 13490,
    13464, 5268, 13487, 5283, 5265, 13469, 5286, 13482,
    5288, 13476, 5279, 13459, 13473, 5293, 13462, 5274,
    5296, 13500, 5255, 13451, 13497, 5301, 13454, 5250,
    13450, 5254, 13501, 5297, 5251, 13455, 5300, 13496,
    13458, 5278, 13477, 5289, 5275, 13463, 5292, 13472,
    5282, 13486, 5269, 13465, 13483, 5287, 13468, 5264,
    5306, 13494, 5261, 13441, 13491, 5311, 13444, 5256]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row15 : Fin 64 → ℕ :=
  ![5056, 5057, 13311, 13310, 5060, 5061, 13307, 13306,
    13264, 13265, 5103, 5102, 13268, 13269, 5099, 5098,
    13256, 13257, 5111, 5110, 13260, 13261, 5107, 5106,
    5080, 5081, 13287, 13286, 5084, 5085, 13283, 13282,
    5088, 5089, 13279, 13278, 5092, 5093, 13275, 13274,
    13296, 13297, 5071, 5070, 13300, 13301, 5067, 5066,
    13288, 13289, 5079, 5078, 13292, 13293, 5075, 5074,
    5112, 5113, 13255, 13254, 5116, 5117, 13251, 13250]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row16 : Fin 64 → ℕ :=
  ![5120, 13324, 5160, 13348, 13321, 5125, 13345, 5165,
    5128, 13316, 5152, 13356, 13313, 5133, 13353, 5157,
    13367, 5179, 13343, 5139, 5182, 13362, 5142, 13338,
    13375, 5171, 13335, 5147, 5174, 13370, 5150, 13330,
    5130, 13318, 5154, 13358, 13315, 5135, 13355, 5159,
    5122, 13326, 5162, 13350, 13323, 5127, 13347, 5167,
    13373, 5169, 13333, 5145, 5172, 13368, 5148, 13328,
    13365, 5177, 13341, 5137, 5180, 13360, 5140, 13336]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row17 : Fin 64 → ℕ :=
  ![13120, 4937, 13128, 4929, 4940, 13125, 4932, 13133,
    13144, 4945, 13136, 4953, 4948, 13149, 4956, 13141,
    4983, 13182, 4991, 13174, 13179, 4978, 13171, 4986,
    4975, 13158, 4967, 13166, 13155, 4970, 13163, 4962,
    13130, 4931, 13122, 4939, 4934, 13135, 4942, 13127,
    13138, 4955, 13146, 4947, 4958, 13143, 4950, 13151,
    4989, 13172, 4981, 13180, 13169, 4984, 13177, 4976,
    4965, 13164, 4973, 13156, 13161, 4960, 13153, 4968]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row18 : Fin 64 → ℕ :=
  ![13184, 13243, 5023, 5028, 13246, 13189, 5025, 5018,
    5055, 4996, 13216, 13211, 4993, 5050, 13214, 13221,
    5047, 5004, 13224, 13203, 5001, 5042, 13206, 13229,
    13192, 13235, 5015, 5036, 13238, 13197, 5033, 5010,
    13231, 13204, 5040, 5003, 13201, 13226, 5006, 5045,
    5008, 5035, 13199, 13236, 5038, 5013, 13233, 13194,
    5016, 5027, 13191, 13244, 5030, 5021, 13241, 13186,
    13223, 13212, 5048, 4995, 13209, 13218, 4998, 5053]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row19 : Fin 64 → ℕ :=
  ![12864, 12926, 12923, 12869, 4735, 4673, 4676, 4730,
    4719, 4689, 4692, 4714, 12880, 12910, 12907, 12885,
    4727, 4681, 4684, 4722, 12872, 12918, 12915, 12877,
    12888, 12902, 12899, 12893, 4711, 4697, 4700, 4706,
    12895, 12897, 12900, 12890, 4704, 4702, 4699, 4709,
    4720, 4686, 4683, 4725, 12879, 12913, 12916, 12874,
    4712, 4694, 4691, 4717, 12887, 12905, 12908, 12882,
    12871, 12921, 12924, 12866, 4728, 4678, 4675, 4733]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row20 : Fin 64 → ℕ :=
  ![12928, 4739, 4742, 12933, 12989, 4798, 4795, 12984,
    12962, 4769, 4772, 12967, 12959, 4764, 4761, 12954,
    12938, 4745, 4748, 12943, 12983, 4788, 4785, 12978,
    12968, 4779, 4782, 12973, 12949, 4758, 4755, 12944,
    4738, 12929, 12932, 4743, 4799, 12988, 12985, 4794,
    4768, 12963, 12966, 4773, 4765, 12958, 12955, 4760,
    4744, 12939, 12942, 4749, 4789, 12982, 12979, 4784,
    4778, 12969, 12972, 4783, 4759, 12948, 12945, 4754]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row21 : Fin 64 → ℕ :=
  ![12736, 4607, 4576, 12767, 12737, 4606, 4577, 12766,
    12740, 4603, 4580, 12763, 12741, 4602, 4581, 12762,
    4552, 12791, 12776, 4567, 4553, 12790, 12777, 4566,
    4556, 12787, 12780, 4563, 4557, 12786, 12781, 4562,
    4546, 12797, 12770, 4573, 4547, 12796, 12771, 4572,
    4550, 12793, 12774, 4569, 4551, 12792, 12775, 4568,
    12746, 4597, 4586, 12757, 12747, 4596, 4587, 12756,
    12750, 4593, 4590, 12753, 12751, 4592, 4591, 12752]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row22 : Fin 64 → ℕ :=
  ![12800, 4617, 4620, 12805, 12808, 4609, 4612, 12813,
    12824, 4625, 4628, 12829, 12816, 4633, 4636, 12821,
    4648, 12833, 12836, 4653, 4640, 12841, 12844, 4645,
    4656, 12857, 12860, 4661, 4664, 12849, 12852, 4669,
    4663, 12862, 12859, 4658, 4671, 12854, 12851, 4666,
    4655, 12838, 12835, 4650, 4647, 12846, 12843, 4642,
    12831, 4630, 4627, 12826, 12823, 4638, 4635, 12818,
    12807, 4622, 4619, 12802, 12815, 4614, 4611, 12810]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row23 : Fin 64 → ℕ :=
  ![4416, 4424, 4456, 4448, 12617, 12609, 12641, 12649,
    12620, 12612, 12644, 12652, 4421, 4429, 4461, 4453,
    12632, 12624, 12656, 12664, 4433, 4441, 4473, 4465,
    4436, 4444, 4476, 4468, 12637, 12629, 12661, 12669,
    12663, 12671, 12639, 12631, 4478, 4470, 4438, 4446,
    4475, 4467, 4435, 4443, 12658, 12666, 12634, 12626,
    4463, 4455, 4423, 4431, 12646, 12654, 12622, 12614,
    12643, 12651, 12619, 12611, 4458, 4450, 4418, 4426]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row24 : Fin 64 → ℕ :=
  ![4480, 4542, 4539, 4485, 12735, 12673, 12676, 12730,
    12719, 12689, 12692, 12714, 4496, 4526, 4523, 4501,
    12727, 12681, 12684, 12722, 4488, 4534, 4531, 4493,
    4504, 4518, 4515, 4509, 12711, 12697, 12700, 12706,
    12733, 12675, 12678, 12728, 4482, 4540, 4537, 4487,
    4498, 4524, 4521, 4503, 12717, 12691, 12694, 12712,
    4490, 4532, 4529, 4495, 12725, 12683, 12686, 12720,
    12709, 12699, 12702, 12704, 4506, 4516, 4513, 4511]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row25 : Fin 64 → ℕ :=
  ![5952, 14176, 14184, 5960, 14192, 5968, 5976, 14200,
    14177, 5953, 5961, 14185, 5969, 14193, 14201, 5977,
    5986, 14146, 14154, 5994, 14162, 6002, 6010, 14170,
    14147, 5987, 5995, 14155, 6003, 14163, 14171, 6011,
    5983, 14207, 14199, 5975, 14191, 5967, 5959, 14183,
    14206, 5982, 5974, 14198, 5966, 14190, 14182, 5958,
    6013, 14173, 14165, 6005, 14157, 5997, 5989, 14149,
    14172, 6012, 6004, 14164, 5996, 14156, 14148, 5988]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row26 : Fin 64 → ℕ :=
  ![6016, 14209, 14224, 6033, 14210, 6019, 6034, 14227,
    14240, 6049, 6064, 14257, 6050, 14243, 14258, 6067,
    6079, 14270, 14255, 6062, 14269, 6076, 6061, 14252,
    14239, 6046, 6031, 14222, 6045, 14236, 14221, 6028,
    6024, 14217, 14232, 6041, 14218, 6027, 6042, 14235,
    14248, 6057, 6072, 14265, 6058, 14251, 14266, 6075,
    6071, 14262, 14247, 6054, 14261, 6068, 6053, 14244,
    14231, 6038, 6023, 14214, 6037, 14228, 14213, 6020]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row27 : Fin 64 → ℕ :=
  ![5824, 5883, 5860, 5855, 5828, 5887, 5856, 5851,
    5844, 5871, 5872, 5835, 5840, 5867, 5876, 5839,
    5836, 5879, 5864, 5843, 5832, 5875, 5868, 5847,
    5848, 5859, 5884, 5831, 5852, 5863, 5880, 5827,
    5830, 5885, 5858, 5849, 5826, 5881, 5862, 5853,
    5842, 5865, 5878, 5837, 5846, 5869, 5874, 5833,
    5834, 5873, 5870, 5845, 5838, 5877, 5866, 5841,
    5854, 5861, 5882, 5825, 5850, 5857, 5886, 5829]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row28 : Fin 64 → ℕ :=
  ![5888, 5889, 5892, 5893, 5890, 5891, 5894, 5895,
    5896, 5897, 5900, 5901, 5898, 5899, 5902, 5903,
    5904, 5905, 5908, 5909, 5906, 5907, 5910, 5911,
    5912, 5913, 5916, 5917, 5914, 5915, 5918, 5919,
    5951, 5950, 5947, 5946, 5949, 5948, 5945, 5944,
    5943, 5942, 5939, 5938, 5941, 5940, 5937, 5936,
    5935, 5934, 5931, 5930, 5933, 5932, 5929, 5928,
    5927, 5926, 5923, 5922, 5925, 5924, 5921, 5920]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row29 : Fin 64 → ℕ :=
  ![5696, 5705, 13905, 13912, 13950, 13943, 5743, 5734,
    5699, 5706, 13906, 13915, 13949, 13940, 5740, 5733,
    5701, 5708, 13908, 13917, 13947, 13938, 5738, 5731,
    5702, 5711, 13911, 13918, 13944, 13937, 5737, 5728,
    13889, 13896, 5712, 5721, 5759, 5750, 13934, 13927,
    13890, 13899, 5715, 5722, 5756, 5749, 13933, 13924,
    13892, 13901, 5717, 5724, 5754, 5747, 13931, 13922,
    13895, 13902, 5718, 5727, 5753, 5744, 13928, 13921]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row30 : Fin 64 → ℕ :=
  ![5760, 13953, 13956, 5765, 5823, 14014, 14011, 5818,
    5792, 13985, 13988, 5797, 5791, 13982, 13979, 5786,
    13954, 5763, 5766, 13959, 14013, 5820, 5817, 14008,
    13986, 5795, 5798, 13991, 13981, 5788, 5785, 13976,
    13960, 5769, 5772, 13965, 14007, 5814, 5811, 14002,
    13992, 5801, 5804, 13997, 13975, 5782, 5779, 13970,
    5770, 13963, 13966, 5775, 5813, 14004, 14001, 5808,
    5802, 13995, 13998, 5807, 5781, 13972, 13969, 5776]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row31 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14308, 6085, 6100, 14325,
    14312, 6089, 6104, 14329, 0, 0, 0, 0,
    0, 0, 0, 0, 6086, 14311, 14326, 6103,
    6090, 14315, 14330, 6107, 0, 0, 0, 0,
    0, 0, 0, 0, 14276, 6117, 6132, 14293,
    14280, 6121, 6136, 14297, 0, 0, 0, 0,
    0, 0, 0, 0, 6118, 14279, 14294, 6135,
    6122, 14283, 14298, 6139, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row32 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14308, 6085, 6100, 14325,
    14312, 6089, 6104, 14329, 0, 0, 0, 0,
    0, 0, 0, 0, 6086, 14311, 14326, 6103,
    6090, 14315, 14330, 6107, 0, 0, 0, 0,
    0, 0, 0, 0, 14276, 6117, 6132, 14293,
    14280, 6121, 6136, 14297, 0, 0, 0, 0,
    0, 0, 0, 0, 6118, 14279, 14294, 6135,
    6122, 14283, 14298, 6139, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row33 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14785, 14789, 6654, 6650,
    14786, 14790, 6653, 6649, 0, 0, 0, 0,
    0, 0, 0, 0, 6601, 6605, 14838, 14834,
    6602, 6606, 14837, 14833, 0, 0, 0, 0,
    0, 0, 0, 0, 14801, 14805, 6638, 6634,
    14802, 14806, 6637, 6633, 0, 0, 0, 0,
    0, 0, 0, 0, 6617, 6621, 14822, 14818,
    6618, 6622, 14821, 14817, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row34 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14785, 14789, 6654, 6650,
    14786, 14790, 6653, 6649, 0, 0, 0, 0,
    0, 0, 0, 0, 6601, 6605, 14838, 14834,
    6602, 6606, 14837, 14833, 0, 0, 0, 0,
    0, 0, 0, 0, 14801, 14805, 6638, 6634,
    14802, 14806, 6637, 6633, 0, 0, 0, 0,
    0, 0, 0, 0, 6617, 6621, 14822, 14818,
    6618, 6622, 14821, 14817, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row35 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6340, 6341, 14564, 14565,
    6344, 6345, 14568, 14569, 0, 0, 0, 0,
    0, 0, 0, 0, 6395, 6394, 14555, 14554,
    6391, 6390, 14551, 14550, 0, 0, 0, 0,
    0, 0, 0, 0, 14534, 14535, 6374, 6375,
    14538, 14539, 6378, 6379, 0, 0, 0, 0,
    0, 0, 0, 0, 14585, 14584, 6361, 6360,
    14581, 14580, 6357, 6356, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row36 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6340, 6341, 14564, 14565,
    6344, 6345, 14568, 14569, 0, 0, 0, 0,
    0, 0, 0, 0, 6395, 6394, 14555, 14554,
    6391, 6390, 14551, 14550, 0, 0, 0, 0,
    0, 0, 0, 0, 14534, 14535, 6374, 6375,
    14538, 14539, 6378, 6379, 0, 0, 0, 0,
    0, 0, 0, 0, 14585, 14584, 6361, 6360,
    14581, 14580, 6357, 6356, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row37 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15046, 6853, 6868, 15063,
    15050, 6857, 6872, 15067, 0, 0, 0, 0,
    0, 0, 0, 0, 6884, 15079, 15094, 6901,
    6888, 15083, 15098, 6905, 0, 0, 0, 0,
    0, 0, 0, 0, 15044, 6855, 6870, 15061,
    15048, 6859, 6874, 15065, 0, 0, 0, 0,
    0, 0, 0, 0, 6886, 15077, 15092, 6903,
    6890, 15081, 15096, 6907, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row38 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15046, 6853, 6868, 15063,
    15050, 6857, 6872, 15067, 0, 0, 0, 0,
    0, 0, 0, 0, 6884, 15079, 15094, 6901,
    6888, 15083, 15098, 6905, 0, 0, 0, 0,
    0, 0, 0, 0, 15044, 6855, 6870, 15061,
    15048, 6859, 6874, 15065, 0, 0, 0, 0,
    0, 0, 0, 0, 6886, 15077, 15092, 6903,
    6890, 15081, 15096, 6907, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row39 : Fin 64 → ℕ :=
  ![0, 14404, 14408, 0, 0, 14405, 14409, 0,
    0, 6228, 6232, 0, 0, 6229, 6233, 0,
    0, 14436, 14440, 0, 0, 14437, 14441, 0,
    0, 6260, 6264, 0, 0, 6261, 6265, 0,
    0, 14459, 14455, 0, 0, 14458, 14454, 0,
    0, 6251, 6247, 0, 0, 6250, 6246, 0,
    0, 14427, 14423, 0, 0, 14426, 14422, 0,
    0, 6219, 6215, 0, 0, 6218, 6214, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row40 : Fin 64 → ℕ :=
  ![0, 14404, 14408, 0, 0, 14405, 14409, 0,
    0, 6228, 6232, 0, 0, 6229, 6233, 0,
    0, 14436, 14440, 0, 0, 14437, 14441, 0,
    0, 6260, 6264, 0, 0, 6261, 6265, 0,
    0, 14459, 14455, 0, 0, 14458, 14454, 0,
    0, 6251, 6247, 0, 0, 6250, 6246, 0,
    0, 14427, 14423, 0, 0, 14426, 14422, 0,
    0, 6219, 6215, 0, 0, 6218, 6214, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row41 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6724, 6740, 14971, 14955,
    6728, 6744, 14967, 14951, 0, 0, 0, 0,
    0, 0, 0, 0, 6725, 6741, 14970, 14954,
    6729, 6745, 14966, 14950, 0, 0, 0, 0,
    0, 0, 0, 0, 6756, 6772, 14939, 14923,
    6760, 6776, 14935, 14919, 0, 0, 0, 0,
    0, 0, 0, 0, 6757, 6773, 14938, 14922,
    6761, 6777, 14934, 14918, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row42 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 6724, 6740, 14971, 14955,
    6728, 6744, 14967, 14951, 0, 0, 0, 0,
    0, 0, 0, 0, 6725, 6741, 14970, 14954,
    6729, 6745, 14966, 14950, 0, 0, 0, 0,
    0, 0, 0, 0, 6756, 6772, 14939, 14923,
    6760, 6776, 14935, 14919, 0, 0, 0, 0,
    0, 0, 0, 0, 6757, 6773, 14938, 14922,
    6761, 6777, 14934, 14918, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row43 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14692, 6469, 14660, 6501,
    14696, 6473, 14664, 6505, 0, 0, 0, 0,
    0, 0, 0, 0, 6470, 14695, 6502, 14663,
    6474, 14699, 6506, 14667, 0, 0, 0, 0,
    0, 0, 0, 0, 6484, 14709, 6516, 14677,
    6488, 14713, 6520, 14681, 0, 0, 0, 0,
    0, 0, 0, 0, 14710, 6487, 14678, 6519,
    14714, 6491, 14682, 6523, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row44 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 14692, 6469, 14660, 6501,
    14696, 6473, 14664, 6505, 0, 0, 0, 0,
    0, 0, 0, 0, 6470, 14695, 6502, 14663,
    6474, 14699, 6506, 14667, 0, 0, 0, 0,
    0, 0, 0, 0, 6484, 14709, 6516, 14677,
    6488, 14713, 6520, 14681, 0, 0, 0, 0,
    0, 0, 0, 0, 14710, 6487, 14678, 6519,
    14714, 6491, 14682, 6523, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row45 : Fin 64 → ℕ :=
  ![0, 15177, 15178, 0, 0, 6981, 6982, 0,
    0, 15169, 15170, 0, 0, 6989, 6990, 0,
    0, 6993, 6994, 0, 0, 15197, 15198, 0,
    0, 7001, 7002, 0, 0, 15189, 15190, 0,
    0, 7038, 7037, 0, 0, 15218, 15217, 0,
    0, 7030, 7029, 0, 0, 15226, 15225, 0,
    0, 15206, 15205, 0, 0, 7018, 7017, 0,
    0, 15214, 15213, 0, 0, 7010, 7009, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row46 : Fin 64 → ℕ :=
  ![0, 15177, 15178, 0, 0, 6981, 6982, 0,
    0, 15169, 15170, 0, 0, 6989, 6990, 0,
    0, 6993, 6994, 0, 0, 15197, 15198, 0,
    0, 7001, 7002, 0, 0, 15189, 15190, 0,
    0, 7038, 7037, 0, 0, 15218, 15217, 0,
    0, 7030, 7029, 0, 0, 15226, 15225, 0,
    0, 15206, 15205, 0, 0, 7018, 7017, 0,
    0, 15214, 15213, 0, 0, 7010, 7009, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row47 : Fin 64 → ℕ :=
  ![0, 16251, 16247, 0, 0, 16212, 16216, 0,
    0, 8004, 8008, 0, 0, 8043, 8039, 0,
    0, 8036, 8040, 0, 0, 8011, 8007, 0,
    0, 16219, 16215, 0, 0, 16244, 16248, 0,
    0, 8006, 8010, 0, 0, 8041, 8037, 0,
    0, 16249, 16245, 0, 0, 16214, 16218, 0,
    0, 16217, 16213, 0, 0, 16246, 16250, 0,
    0, 8038, 8042, 0, 0, 8009, 8005, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row48 : Fin 64 → ℕ :=
  ![0, 16251, 16247, 0, 0, 16212, 16216, 0,
    0, 8004, 8008, 0, 0, 8043, 8039, 0,
    0, 8036, 8040, 0, 0, 8011, 8007, 0,
    0, 16219, 16215, 0, 0, 16244, 16248, 0,
    0, 8006, 8010, 0, 0, 8041, 8037, 0,
    0, 16249, 16245, 0, 0, 16214, 16218, 0,
    0, 16217, 16213, 0, 0, 16246, 16250, 0,
    0, 8038, 8042, 0, 0, 8009, 8005, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row49 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7497, 15685, 7521, 15725,
    7498, 15686, 7522, 15726, 0, 0, 0, 0,
    0, 0, 0, 0, 7489, 15693, 7529, 15717,
    7490, 15694, 7530, 15718, 0, 0, 0, 0,
    0, 0, 0, 0, 7505, 15709, 7545, 15733,
    7506, 15710, 7546, 15734, 0, 0, 0, 0,
    0, 0, 0, 0, 7513, 15701, 7537, 15741,
    7514, 15702, 7538, 15742, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row50 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7497, 15685, 7521, 15725,
    7498, 15686, 7522, 15726, 0, 0, 0, 0,
    0, 0, 0, 0, 7489, 15693, 7529, 15717,
    7490, 15694, 7530, 15718, 0, 0, 0, 0,
    0, 0, 0, 0, 7505, 15709, 7545, 15733,
    7506, 15710, 7546, 15734, 0, 0, 0, 0,
    0, 0, 0, 0, 7513, 15701, 7537, 15741,
    7514, 15702, 7538, 15742, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row51 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7780, 7749, 15995, 15962,
    7784, 7753, 15991, 15958, 0, 0, 0, 0,
    0, 0, 0, 0, 15940, 15973, 7771, 7802,
    15944, 15977, 7767, 7798, 0, 0, 0, 0,
    0, 0, 0, 0, 15956, 15989, 7755, 7786,
    15960, 15993, 7751, 7782, 0, 0, 0, 0,
    0, 0, 0, 0, 7796, 7765, 15979, 15946,
    7800, 7769, 15975, 15942, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row52 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7780, 7749, 15995, 15962,
    7784, 7753, 15991, 15958, 0, 0, 0, 0,
    0, 0, 0, 0, 15940, 15973, 7771, 7802,
    15944, 15977, 7767, 7798, 0, 0, 0, 0,
    0, 0, 0, 0, 15956, 15989, 7755, 7786,
    15960, 15993, 7751, 7782, 0, 0, 0, 0,
    0, 0, 0, 0, 7796, 7765, 15979, 15946,
    7800, 7769, 15975, 15942, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row53 : Fin 64 → ℕ :=
  ![0, 7252, 7256, 0, 0, 15429, 15433, 0,
    0, 7236, 7240, 0, 0, 15445, 15449, 0,
    0, 7268, 7272, 0, 0, 15477, 15481, 0,
    0, 7284, 7288, 0, 0, 15461, 15465, 0,
    0, 7238, 7242, 0, 0, 15447, 15451, 0,
    0, 7254, 7258, 0, 0, 15431, 15435, 0,
    0, 7286, 7290, 0, 0, 15463, 15467, 0,
    0, 7270, 7274, 0, 0, 15479, 15483, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row54 : Fin 64 → ℕ :=
  ![0, 7252, 7256, 0, 0, 15429, 15433, 0,
    0, 7236, 7240, 0, 0, 15445, 15449, 0,
    0, 7268, 7272, 0, 0, 15477, 15481, 0,
    0, 7284, 7288, 0, 0, 15461, 15465, 0,
    0, 7238, 7242, 0, 0, 15447, 15451, 0,
    0, 7254, 7258, 0, 0, 15431, 15435, 0,
    0, 7286, 7290, 0, 0, 15463, 15467, 0,
    0, 7270, 7274, 0, 0, 15479, 15483, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row55 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 16070, 16123, 16100, 16089,
    16074, 16119, 16104, 16085, 0, 0, 0, 0,
    0, 0, 0, 0, 7877, 7928, 7911, 7898,
    7881, 7924, 7915, 7894, 0, 0, 0, 0,
    0, 0, 0, 0, 16068, 16121, 16102, 16091,
    16072, 16117, 16106, 16087, 0, 0, 0, 0,
    0, 0, 0, 0, 7879, 7930, 7909, 7896,
    7883, 7926, 7913, 7892, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row56 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 16070, 16123, 16100, 16089,
    16074, 16119, 16104, 16085, 0, 0, 0, 0,
    0, 0, 0, 0, 7877, 7928, 7911, 7898,
    7881, 7924, 7915, 7894, 0, 0, 0, 0,
    0, 0, 0, 0, 16068, 16121, 16102, 16091,
    16072, 16117, 16106, 16087, 0, 0, 0, 0,
    0, 0, 0, 0, 7879, 7930, 7909, 7896,
    7883, 7926, 7913, 7892, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row57 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15572, 7365, 15611, 7402,
    15576, 7369, 15607, 7398, 0, 0, 0, 0,
    0, 0, 0, 0, 15588, 7413, 15563, 7386,
    15592, 7417, 15559, 7382, 0, 0, 0, 0,
    0, 0, 0, 0, 7364, 15573, 7403, 15610,
    7368, 15577, 7399, 15606, 0, 0, 0, 0,
    0, 0, 0, 0, 7412, 15589, 7387, 15562,
    7416, 15593, 7383, 15558, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row58 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15572, 7365, 15611, 7402,
    15576, 7369, 15607, 7398, 0, 0, 0, 0,
    0, 0, 0, 0, 15588, 7413, 15563, 7386,
    15592, 7417, 15559, 7382, 0, 0, 0, 0,
    0, 0, 0, 0, 7364, 15573, 7403, 15610,
    7368, 15577, 7399, 15606, 0, 0, 0, 0,
    0, 0, 0, 0, 7412, 15589, 7387, 15562,
    7416, 15593, 7383, 15558, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row59 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15844, 7636, 15812, 7668,
    15848, 7640, 15816, 7672, 0, 0, 0, 0,
    0, 0, 0, 0, 7675, 15819, 7643, 15851,
    7671, 15815, 7639, 15847, 0, 0, 0, 0,
    0, 0, 0, 0, 15814, 7670, 15846, 7638,
    15818, 7674, 15850, 7642, 0, 0, 0, 0,
    0, 0, 0, 0, 7641, 15849, 7673, 15817,
    7637, 15845, 7669, 15813, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row60 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 15844, 7636, 15812, 7668,
    15848, 7640, 15816, 7672, 0, 0, 0, 0,
    0, 0, 0, 0, 7675, 15819, 7643, 15851,
    7671, 15815, 7639, 15847, 0, 0, 0, 0,
    0, 0, 0, 0, 15814, 7670, 15846, 7638,
    15818, 7674, 15850, 7642, 0, 0, 0, 0,
    0, 0, 0, 0, 7641, 15849, 7673, 15817,
    7637, 15845, 7669, 15813, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row61 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7113, 7166, 7137, 7126,
    7114, 7165, 7138, 7125, 0, 0, 0, 0,
    0, 0, 0, 0, 15301, 15346, 15341, 15322,
    15302, 15345, 15342, 15321, 0, 0, 0, 0,
    0, 0, 0, 0, 7121, 7142, 7161, 7118,
    7122, 7141, 7162, 7117, 0, 0, 0, 0,
    0, 0, 0, 0, 15325, 15338, 15349, 15298,
    15326, 15337, 15350, 15297, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase octad target addresses. -/
def generatedFourthMonomialOctadWord2Row62 : Fin 64 → ℕ :=
  ![0, 0, 0, 0, 7113, 7166, 7137, 7126,
    7114, 7165, 7138, 7125, 0, 0, 0, 0,
    0, 0, 0, 0, 15301, 15346, 15341, 15322,
    15302, 15345, 15342, 15321, 0, 0, 0, 0,
    0, 0, 0, 0, 7121, 7142, 7161, 7118,
    7122, 7141, 7162, 7117, 0, 0, 0, 0,
    0, 0, 0, 0, 15325, 15338, 15349, 15298,
    15326, 15337, 15350, 15297, 0, 0, 0, 0]

/-- Literal candidate octad target addresses, with the target central phase retained. -/
def generatedFourthMonomialShortOctadTargets2 : Fin 63 → Fin 64 → ℕ :=
  ![
    generatedFourthMonomialOctadWord2Row0,
    generatedFourthMonomialOctadWord2Row1,
    generatedFourthMonomialOctadWord2Row2,
    generatedFourthMonomialOctadWord2Row3,
    generatedFourthMonomialOctadWord2Row4,
    generatedFourthMonomialOctadWord2Row5,
    generatedFourthMonomialOctadWord2Row6,
    generatedFourthMonomialOctadWord2Row7,
    generatedFourthMonomialOctadWord2Row8,
    generatedFourthMonomialOctadWord2Row9,
    generatedFourthMonomialOctadWord2Row10,
    generatedFourthMonomialOctadWord2Row11,
    generatedFourthMonomialOctadWord2Row12,
    generatedFourthMonomialOctadWord2Row13,
    generatedFourthMonomialOctadWord2Row14,
    generatedFourthMonomialOctadWord2Row15,
    generatedFourthMonomialOctadWord2Row16,
    generatedFourthMonomialOctadWord2Row17,
    generatedFourthMonomialOctadWord2Row18,
    generatedFourthMonomialOctadWord2Row19,
    generatedFourthMonomialOctadWord2Row20,
    generatedFourthMonomialOctadWord2Row21,
    generatedFourthMonomialOctadWord2Row22,
    generatedFourthMonomialOctadWord2Row23,
    generatedFourthMonomialOctadWord2Row24,
    generatedFourthMonomialOctadWord2Row25,
    generatedFourthMonomialOctadWord2Row26,
    generatedFourthMonomialOctadWord2Row27,
    generatedFourthMonomialOctadWord2Row28,
    generatedFourthMonomialOctadWord2Row29,
    generatedFourthMonomialOctadWord2Row30,
    generatedFourthMonomialOctadWord2Row31,
    generatedFourthMonomialOctadWord2Row32,
    generatedFourthMonomialOctadWord2Row33,
    generatedFourthMonomialOctadWord2Row34,
    generatedFourthMonomialOctadWord2Row35,
    generatedFourthMonomialOctadWord2Row36,
    generatedFourthMonomialOctadWord2Row37,
    generatedFourthMonomialOctadWord2Row38,
    generatedFourthMonomialOctadWord2Row39,
    generatedFourthMonomialOctadWord2Row40,
    generatedFourthMonomialOctadWord2Row41,
    generatedFourthMonomialOctadWord2Row42,
    generatedFourthMonomialOctadWord2Row43,
    generatedFourthMonomialOctadWord2Row44,
    generatedFourthMonomialOctadWord2Row45,
    generatedFourthMonomialOctadWord2Row46,
    generatedFourthMonomialOctadWord2Row47,
    generatedFourthMonomialOctadWord2Row48,
    generatedFourthMonomialOctadWord2Row49,
    generatedFourthMonomialOctadWord2Row50,
    generatedFourthMonomialOctadWord2Row51,
    generatedFourthMonomialOctadWord2Row52,
    generatedFourthMonomialOctadWord2Row53,
    generatedFourthMonomialOctadWord2Row54,
    generatedFourthMonomialOctadWord2Row55,
    generatedFourthMonomialOctadWord2Row56,
    generatedFourthMonomialOctadWord2Row57,
    generatedFourthMonomialOctadWord2Row58,
    generatedFourthMonomialOctadWord2Row59,
    generatedFourthMonomialOctadWord2Row60,
    generatedFourthMonomialOctadWord2Row61,
    generatedFourthMonomialOctadWord2Row62
  ]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row0 : Fin 24 → ℕ :=
  ![0, 576, 9248, 9104, 0, 0, 0, 0,
    0, 0, 0, 0, 48, 624, 9152, 8960,
    8912, 816, 1104, 8336, 8864, 1008, 8288, 864]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row1 : Fin 24 → ℕ :=
  ![0, 0, 9272, 9128, 0, 0, 0, 0,
    0, 0, 0, 0, 578, 648, 9176, 8984,
    8936, 840, 1128, 8774, 8888, 1032, 8772, 888]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 1094, 0, 0, 0, 0,
    0, 0, 0, 0, 9250, 9274, 1096, 1088,
    1086, 9282, 9340, 1062, 1084, 9290, 1060, 9284]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 9106, 9130, 998, 944,
    942, 9138, 9334, 918, 940, 9238, 916, 9140]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 440, 344, 296,
    392, 248, 488, 536, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 446, 444,
    448, 442, 498, 546, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 348,
    398, 346, 494, 542, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    396, 298, 492, 540, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 394, 496, 544, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 490, 538, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 548, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 626, 9154, 8962,
    8914, 818, 1106, 8338, 8866, 1010, 8290, 866]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 9178, 8986,
    8938, 842, 1130, 8822, 8890, 1034, 8820, 890]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 992,
    990, 9186, 9336, 966, 988, 9240, 964, 9188]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    798, 9040, 9328, 774, 796, 9232, 772, 9088]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 9038, 9326, 726, 748, 9230, 724, 9086]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1138, 9014, 9036, 1042, 9012, 898]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 9302, 9324, 1146, 9300, 1140]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 678, 9206, 148, 9062]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9228, 676, 9084]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 9204, 1044]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 9060]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign0Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row0 : Fin 24 → ℕ :=
  ![0, 577, 9249, 9105, 0, 0, 0, 0,
    0, 0, 0, 0, 49, 625, 9153, 8961,
    8913, 817, 1105, 8337, 8865, 1009, 8289, 865]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row1 : Fin 24 → ℕ :=
  ![0, 0, 9273, 9129, 0, 0, 0, 0,
    0, 0, 0, 0, 579, 649, 9177, 8985,
    8937, 841, 1129, 8775, 8889, 1033, 8773, 889]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row2 : Fin 24 → ℕ :=
  ![0, 0, 0, 1095, 0, 0, 0, 0,
    0, 0, 0, 0, 9251, 9275, 1097, 1089,
    1087, 9283, 9341, 1063, 1085, 9291, 1061, 9285]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row3 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 9107, 9131, 999, 945,
    943, 9139, 9335, 919, 941, 9239, 917, 9141]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row4 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 441, 345, 297,
    393, 249, 489, 537, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row5 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 447, 445,
    449, 443, 499, 547, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row6 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 349,
    399, 347, 495, 543, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row7 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    397, 299, 493, 541, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row8 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 395, 497, 545, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row9 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 491, 539, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row10 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 549, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row11 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row12 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 627, 9155, 8963,
    8915, 819, 1107, 8339, 8867, 1011, 8291, 867]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row13 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 9179, 8987,
    8939, 843, 1131, 8823, 8891, 1035, 8821, 891]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row14 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 993,
    991, 9187, 9337, 967, 989, 9241, 965, 9189]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row15 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    799, 9041, 9329, 775, 797, 9233, 773, 9089]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row16 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 9039, 9327, 727, 749, 9231, 725, 9087]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row17 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1139, 9015, 9037, 1043, 9013, 899]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row18 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 9303, 9325, 1147, 9301, 1141]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row19 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 679, 9207, 149, 9063]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row20 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 9229, 677, 9085]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row21 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 9205, 1045]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row22 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 9061]

/-- One bounded row of candidate full-phase pair target addresses. -/
def generatedFourthMonomialPairWord2Sign1Row23 : Fin 24 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

/-- Literal candidate pair target addresses for both original preferred signs. -/
def generatedFourthMonomialShortPairTargets2 : Fin 2 → Fin 24 → Fin 24 → ℕ :=
  ![
    ![generatedFourthMonomialPairWord2Sign0Row0,
    generatedFourthMonomialPairWord2Sign0Row1,
    generatedFourthMonomialPairWord2Sign0Row2,
    generatedFourthMonomialPairWord2Sign0Row3,
    generatedFourthMonomialPairWord2Sign0Row4,
    generatedFourthMonomialPairWord2Sign0Row5,
      generatedFourthMonomialPairWord2Sign0Row6,
    generatedFourthMonomialPairWord2Sign0Row7,
    generatedFourthMonomialPairWord2Sign0Row8,
    generatedFourthMonomialPairWord2Sign0Row9,
    generatedFourthMonomialPairWord2Sign0Row10,
    generatedFourthMonomialPairWord2Sign0Row11,
      generatedFourthMonomialPairWord2Sign0Row12,
    generatedFourthMonomialPairWord2Sign0Row13,
    generatedFourthMonomialPairWord2Sign0Row14,
    generatedFourthMonomialPairWord2Sign0Row15,
    generatedFourthMonomialPairWord2Sign0Row16,
    generatedFourthMonomialPairWord2Sign0Row17,
      generatedFourthMonomialPairWord2Sign0Row18,
    generatedFourthMonomialPairWord2Sign0Row19,
    generatedFourthMonomialPairWord2Sign0Row20,
    generatedFourthMonomialPairWord2Sign0Row21,
    generatedFourthMonomialPairWord2Sign0Row22,
    generatedFourthMonomialPairWord2Sign0Row23],
    ![generatedFourthMonomialPairWord2Sign1Row0,
    generatedFourthMonomialPairWord2Sign1Row1,
    generatedFourthMonomialPairWord2Sign1Row2,
    generatedFourthMonomialPairWord2Sign1Row3,
    generatedFourthMonomialPairWord2Sign1Row4,
    generatedFourthMonomialPairWord2Sign1Row5,
      generatedFourthMonomialPairWord2Sign1Row6,
    generatedFourthMonomialPairWord2Sign1Row7,
    generatedFourthMonomialPairWord2Sign1Row8,
    generatedFourthMonomialPairWord2Sign1Row9,
    generatedFourthMonomialPairWord2Sign1Row10,
    generatedFourthMonomialPairWord2Sign1Row11,
      generatedFourthMonomialPairWord2Sign1Row12,
    generatedFourthMonomialPairWord2Sign1Row13,
    generatedFourthMonomialPairWord2Sign1Row14,
    generatedFourthMonomialPairWord2Sign1Row15,
    generatedFourthMonomialPairWord2Sign1Row16,
    generatedFourthMonomialPairWord2Sign1Row17,
      generatedFourthMonomialPairWord2Sign1Row18,
    generatedFourthMonomialPairWord2Sign1Row19,
    generatedFourthMonomialPairWord2Sign1Row20,
    generatedFourthMonomialPairWord2Sign1Row21,
    generatedFourthMonomialPairWord2Sign1Row22,
    generatedFourthMonomialPairWord2Sign1Row23]
  ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
