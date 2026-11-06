/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerIncomingTree

/-! Exact incoming octad candidate records; source equality is certified separately. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original octad address is the lowest ten bits of its exact sparse record. -/
def generatedTenthFinalSourceOctadSparseKey (word : ℕ) : ℕ := word % 1024

set_option maxRecDepth 100000 in
-- Elaborate the complete balanced tree containing every original octad, including zeros.
/-- All 759 original octads retain their signed source slots and zero records. -/
def generatedTenthFinalSourceOctadSparseTree : GeneratedNinthIncomingTree ℕ :=
  (.node 2248283654523
    (.node 2246672730301
      (.node 2239689214046
        (.node 2173922904111
          (.node 2236736522263
            (.node 2238883874827
              (.node 161754467702588044370298296325
                (.node 161793155670400343818547255298
                  (.node 2166137866241
                    (.node 2168822269952
                      .empty
                      .empty)
                    .empty)
                  (.node 2166137866244
                    (.node 157150603083976128895404513283
                      .empty
                      .empty)
                    .empty))
                (.node 602941528923495829512
                  (.node 11321106086297502001415966410204640897918953479
                    (.node 162122009487536296107853649926
                      .empty
                      .empty)
                    .empty)
                  (.node 2239693522954
                    (.node 2242105296905
                      .empty
                      .empty)
                    .empty)))
              (.node 2242910537745
                (.node 2178486421518
                  (.node 2178486568973
                    (.node 2180902340620
                      .empty
                      .empty)
                    .empty)
                  (.node 2176606930960
                    (.node 2180902488079
                      .empty
                      .empty)
                    .empty))
                (.node 2243988752404
                  (.node 2247209977875
                    (.node 2180902078482
                      .empty
                      .empty)
                    .empty)
                  (.node 2235666843670
                    (.node 2174463821845
                      .empty
                      .empty)
                    .empty))))
            (.node 157150585376615102377701185571
              (.node 2695821046017662017157076009704477
                (.node 157111916297982760162905577498
                  (.node 2180902225945
                    (.node 2247209830424
                      .empty
                      .empty)
                    .empty)
                  (.node 2240494585884
                    (.node 2167211640859
                      .empty
                      .empty)
                    .empty))
                (.node 161986602709451382027676833824
                  (.node 162063978687083504580679784479
                    (.node 157189581498943426817106728990
                      .empty
                      .empty)
                    .empty)
                  (.node 162102661933391918895441958946
                    (.node 2235935311905
                      .empty
                      .empty)
                    .empty)))
              (.node 157169938834726442350794020905
                (.node 603445962802324492326
                  (.node 603447035925673152549
                    (.node 604023571516435779620
                      .empty
                      .empty)
                    .empty)
                  (.node 156976503619244507985105524776
                    (.node 585431581958848761895
                      .empty
                      .empty)
                    .empty))
                (.node 2177143982124
                  (.node 2178486569003
                    (.node 2178486306858
                      .empty
                      .empty)
                    .empty)
                  (.node 2250162505774
                    (.node 2246941132845
                      .empty
                      .empty)
                    .empty)))))
          (.node 157150580654248619506982230087
            (.node 2175268898875
              (.node 53
                (.node 603879434333563588658
                  (.node 2249625749553
                    (.node 2249626011696
                      .empty
                      .empty)
                    .empty)
                  (.node 2176607258676
                    (.node 2181175183411
                      .empty
                      .empty)
                    .empty))
                (.node 2168826382392
                  (.node 2242914863159
                    (.node 54
                      .empty
                      .empty)
                    .empty)
                  (.node 2240226117690
                    (.node 584782993170748198969
                      .empty
                      .empty)
                    .empty)))
              (.node 2179023308865
                (.node 62
                  (.node 157111912754622521053223704637
                    (.node 60
                      .empty
                      .empty)
                    .empty)
                  (.node 2178754693184
                    (.node 157073224767427797460795365439
                      .empty
                      .empty)
                    .empty))
                (.node 161928565989107084260756494404
                  (.node 584784167517882077251
                    (.node 603373874422229471298
                      .empty
                      .empty)
                    .empty)
                  (.node 162102349094123470792033376326
                    (.node 156976797586125721123132840005
                      .empty
                      .empty)
                    .empty))))
            (.node 2247210240083
              (.node 2245330929741
                (.node 585431564366662275146
                  (.node 584928243123006509129
                    (.node 585432633085253521480
                      .empty
                      .empty)
                    .empty)
                  (.node 76
                    (.node 2177680574539
                      .empty
                      .empty)
                    .empty))
                (.node 2250162554960
                  (.node 79
                    (.node 2174191192142
                      .empty
                      .empty)
                    .empty)
                  (.node 2247210240082
                    (.node 603229741712830156881
                      .empty
                      .empty)
                    .empty)))
              (.node 2180902340697
                (.node 2242373683286
                  (.node 2245594761301
                    (.node 2177953482836
                      .empty
                      .empty)
                    .empty)
                  (.node 2180902340696
                    (.node 2181174855767
                      .empty
                      .empty)
                    .empty))
                (.node 2179023046748
                  (.node 91
                    (.node 157111912755775512857851058266
                      .empty
                      .empty)
                    .empty)
                  (.node 2179828631645
                    .empty
                    .empty))))))
        (.node 2246131779726
          (.node 118
            (.node 2237277620330
              (.node 11677940384410469282607797742011583938932303972
                (.node 97
                  (.node 157073224750132919291806324832
                    (.node 2174732126303
                      .empty
                      .empty)
                    .empty)
                  (.node 162083320319749947399699011683
                    (.node 161677098811317097358017452130
                      .empty
                      .empty)
                    .empty))
                (.node 13372211215748004560266986174979247128335832564885740708012153125991
                  (.node 43498524772232303629167413532245155942
                    (.node 601789684872907067493
                      .empty
                      .empty)
                    .empty)
                  (.node 161773816419309679047766022249
                    (.node 156802412396389499860307433576
                      .empty
                      .empty)
                    .empty)))
              (.node 112
                (.node 584710913582984007789
                  (.node 603230924714063138924
                    (.node 2178218215531
                      .empty
                      .empty)
                    .empty)
                  (.node 2180902291567
                    (.node 2246131632238
                      .empty
                      .empty)
                    .empty))
                (.node 2242109294707
                  (.node 2180906731634
                    (.node 113
                      .empty
                      .empty)
                    .empty)
                  (.node 2168553949301
                    (.node 2178218215540
                      .empty
                      .empty)
                    .empty))))
            (.node 2249894168706
              (.node 2166406334588
                (.node 603229803289239900281
                  (.node 602798434013226930296
                    (.node 119
                      .empty
                      .empty)
                    .empty)
                  (.node 2174996269179
                    (.node 157111916280111262977440962682
                      .empty
                      .empty)
                    .empty))
                (.node 157111912735237849510758652031
                  (.node 2166406334590
                    (.node 157092568762286248524184623229
                      .empty
                      .empty)
                    .empty)
                  (.node 162083320300004913188444412033
                    (.node 2655256226961474403695035161074816
                      .empty
                      .empty)
                    .empty)))
              (.node 603951535840425185416
                (.node 2249894430853
                  (.node 2174728226948
                    (.node 2249894037635
                      .empty
                      .empty)
                    .empty)
                  (.node 135
                    (.node 2180633921670
                      .empty
                      .empty)
                    .empty))
                (.node 585575648697008705675
                  (.node 2249352988810
                    (.node 2174459381897
                      .empty
                      .empty)
                    .empty)
                  (.node 2243183315085
                    (.node 140
                      .empty
                      .empty)
                    .empty)))))
          (.node 2171238418598
            (.node 154
              (.node 2181170759828
                (.node 2167480092817
                  (.node 144
                    (.node 603879465127678414991
                      .empty
                      .empty)
                    .empty)
                  (.node 2238351181971
                    (.node 2246937495698
                      .empty
                      .empty)
                    .empty))
                (.node 2176338823319
                  (.node 2241031637142
                    (.node 2173926803605
                      .empty
                      .empty)
                    .empty)
                  (.node 2234857310361
                    (.node 2176338626712
                      .empty
                      .empty)
                    .empty)))
              (.node 2242646411424
                (.node 2173922740381
                  (.node 2179296151708
                    (.node 585503599894768865435
                      .empty
                      .empty)
                    .empty)
                  (.node 159
                    (.node 2177680672926
                      .empty
                      .empty)
                    .empty))
                (.node 2167480092835
                  (.node 2246941837474
                    (.node 585432668203590553761
                      .empty
                      .empty)
                    .empty)
                  (.node 602581131001069605029
                    (.node 164
                      .empty
                      .empty)
                    .empty))))
            (.node 603807394334396190898
              (.node 2249894299820
                (.node 169
                  (.node 583125620192173904040
                    (.node 2172312094887
                      .empty
                      .empty)
                    .empty)
                  (.node 2176875317419
                    (.node 2246941821098
                      .empty
                      .empty)
                    .empty))
                (.node 2243988670639
                  (.node 174
                    (.node 2246941821101
                      .empty
                      .empty)
                    .empty)
                  (.node 603591129122174161073
                    (.node 2248547633328
                      .empty
                      .empty)
                    .empty)))
              (.node 184
                (.node 181
                  (.node 2175264737460
                    (.node 2243988408499
                      .empty
                      .empty)
                    .empty)
                  (.node 584135517155524399287
                    (.node 2178490812598
                      .empty
                      .empty)
                    .empty))
                (.node 2176875710651
                  (.node 603951417092628238522
                    (.node 2248821000377
                      .empty
                      .empty)
                    .empty)
                  (.node 188
                    .empty
                    .empty)))))))
      (.node 2243984574748
        (.node 2245867505901
          (.node 2175805769941
            (.node 2245331126473
              (.node 2171506821315
                (.node 603230806035790876864
                  (.node 2237541714111
                    (.node 2245599381694
                      .empty
                      .empty)
                    .empty)
                  (.node 2246941558978
                    (.node 193
                      .empty
                      .empty)
                    .empty))
                (.node 2235935246534
                  (.node 2245599119557
                    (.node 2178217560260
                      .empty
                      .empty)
                    .empty)
                  (.node 2245326653640
                    (.node 2242105428167
                      .empty
                      .empty)
                    .empty)))
              (.node 2172043774159
                (.node 2248821000396
                  (.node 203
                    (.node 2246941362378
                      .empty
                      .empty)
                    .empty)
                  (.node 585575727859161682126
                    (.node 585215356323399504077
                      .empty
                      .empty)
                    .empty))
                (.node 162121695449084233402267359442
                  (.node 2173117450449
                    (.node 208
                      .empty
                      .empty)
                    .empty)
                  (.node 2244525770964
                    (.node 2244525770963
                      .empty
                      .empty)
                    .empty))))
            (.node 2249089452257
              (.node 219
                (.node 216
                  (.node 584351685609653407959
                    (.node 603807420659593138390
                      .empty
                      .empty)
                    .empty)
                  (.node 218
                    (.node 217
                      .empty
                      .empty)
                    .empty))
                (.node 2180097329374
                  (.node 600779686751273816285
                    (.node 585071302717370487004
                      .empty
                      .empty)
                    .empty)
                  (.node 35582435425094880
                    (.node 223
                      .empty
                      .empty)
                    .empty)))
              (.node 231
                (.node 2180369385700
                  (.node 2241572538595
                    (.node 226
                      .empty
                      .empty)
                    .empty)
                  (.node 602941550913728368870
                    (.node 229
                      .empty
                      .empty)
                    .empty))
                (.node 2249084930282
                  (.node 603373922803157307625
                    (.node 232
                      .empty
                      .empty)
                    .empty)
                  (.node 236
                    (.node 235
                      .empty
                      .empty)
                    .empty)))))
          (.node 261
            (.node 156879780090064452224872110329
              (.node 162121997662379497462096287987
                (.node 240
                  (.node 239
                    (.node 603085556151182512366
                      .empty
                      .empty)
                    .empty)
                  (.node 2240498993394
                    (.node 584928221064587333873
                      .empty
                      .empty)
                    .empty))
                (.node 2250431727862
                  (.node 2175802099957
                    (.node 2171775109364
                      .empty
                      .empty)
                    .empty)
                  (.node 2237541845240
                    (.node 36796229690117367
                      .empty
                      .empty)
                    .empty)))
              (.node 585360676581588570367
                (.node 2242642086140
                  (.node 251
                    (.node 250
                      .empty
                      .empty)
                    .empty)
                  (.node 601789684941089624318
                    (.node 584350608019538710781
                      .empty
                      .empty)
                    .empty))
                (.node 258
                  (.node 584351760381007597825
                    (.node 256
                      .empty
                      .empty)
                    .empty)
                  (.node 603806294816866767108
                    (.node 585000186294011236611
                      .empty
                      .empty)
                    .empty))))
            (.node 2246941821201
              (.node 267
                (.node 2179291646216
                  (.node 263
                    (.node 601428222622155542790
                      .empty
                      .empty)
                    .empty)
                  (.node 2241568426250
                    (.node 265
                      .empty
                      .empty)
                    .empty))
                (.node 2172584659214
                  (.node 2249626372365
                    (.node 268
                      .empty
                      .empty)
                    .empty)
                  (.node 2245599381776
                    (.node 2242105329935
                      .empty
                      .empty)
                    .empty)))
              (.node 2241841088791
                (.node 2178218150164
                  (.node 584350612418927300883
                    (.node 602941458552608313618
                      .empty
                      .empty)
                    .empty)
                  (.node 601213171340555637014
                    (.node 585504681817163387157
                      .empty
                      .empty)
                    .empty))
                (.node 2173658450202
                  (.node 281
                    (.node 2246941559064
                      .empty
                      .empty)
                    .empty)
                  (.node 2180096510235
                    .empty
                    .empty))))))
        (.node 332
          (.node 308
            (.node 603375035577912545576
              (.node 290
                (.node 2235935312159
                  (.node 286
                    (.node 285
                      .empty
                      .empty)
                    .empty)
                  (.node 603302986709637452065
                    (.node 288
                      .empty
                      .empty)
                    .empty))
                (.node 2173117532453
                  (.node 2179828271396
                    (.node 291
                      .empty
                      .empty)
                    .empty)
                  (.node 2175264868647
                    (.node 294
                      .empty
                      .empty)
                    .empty)))
              (.node 2250158344494
                (.node 2248552073515
                  (.node 2248552335658
                    (.node 2234857326889
                      .empty
                      .empty)
                    .empty)
                  (.node 602870614756056748333
                    (.node 584134466028582244652
                      .empty
                      .empty)
                    .empty))
                (.node 2236472117553
                  (.node 2173654288688
                    (.node 2181438654767
                      .empty
                      .empty)
                    .empty)
                  (.node 2167211641139
                    (.node 603301860878450086194
                      .empty
                      .empty)
                    .empty))))
            (.node 320
              (.node 2248552073530
                (.node 603374987198591144247
                  (.node 310
                    (.node 309
                      .empty
                      .empty)
                    .empty)
                  (.node 2248551811385
                    (.node 2249893955896
                      .empty
                      .empty)
                    .empty))
                (.node 2175264868669
                  (.node 316
                    (.node 585504681817163518267
                      .empty
                      .empty)
                    .empty)
                  (.node 2248279853375
                    (.node 2243984345406
                      .empty
                      .empty)
                    .empty)))
              (.node 326
                (.node 2240226019651
                  (.node 2250163161410
                    (.node 2169359059265
                      .empty
                      .empty)
                    .empty)
                  (.node 2250162325829
                    (.node 603590113181747990852
                      .empty
                      .empty)
                    .empty))
                (.node 2249622178121
                  (.node 2241304136008
                    (.node 2172848949575
                      .empty
                      .empty)
                    .empty)
                  (.node 331
                    (.node 330
                      .empty
                      .empty)
                    .empty)))))
          (.node 2236740700516
            (.node 344
              (.node 338
                (.node 2180097329487
                  (.node 2249889941838
                    (.node 2176879675725
                      .empty
                      .empty)
                    .empty)
                  (.node 337
                    (.node 2250431039824
                      .empty
                      .empty)
                    .empty))
                (.node 162025271790605885250671335765
                  (.node 2246941329748
                    (.node 2248821000531
                      .empty
                      .empty)
                    .empty)
                  (.node 343
                    (.node 157189287550292740984576956758
                      .empty
                      .empty)
                    .empty)))
              (.node 161889878019997677609354991966
                (.node 347
                  (.node 162141339313349580786166159706
                    (.node 162141021733627138252250044761
                      .empty
                      .empty)
                    .empty)
                  (.node 157189593305076888621107140957
                    (.node 348
                      .empty
                      .empty)
                    .empty))
                (.node 353
                  (.node 2168017029472
                    (.node 2181170202975
                      .empty
                      .empty)
                    .empty)
                  (.node 2177681017187
                    (.node 354
                      .empty
                      .empty)
                    .empty))))
            (.node 582837372157268480368
              (.node 2166406302058
                (.node 359
                  (.node 2242641922406
                    (.node 2178222115173
                      .empty
                      .empty)
                    .empty)
                  (.node 361
                    (.node 360
                      .empty
                      .empty)
                    .empty))
                (.node 365
                  (.node 2246400559468
                    (.node 2243984656747
                      .empty
                      .empty)
                    .empty)
                  (.node 2236472117615
                    (.node 2241572604270
                      .empty
                      .empty)
                    .empty)))
              (.node 2250431662454
                (.node 371
                  (.node 2177949206898
                    (.node 2181443062129
                      .empty
                      .empty)
                    .empty)
                  (.node 2244256729461
                    (.node 2246404606324
                      .empty
                      .empty)
                    .empty))
                (.node 2249084406137
                  (.node 585360562227282874744
                    (.node 375
                      .empty
                      .empty)
                    .empty)
                  (.node 2248283392378
                    .empty
                    .empty))))))))
    (.node 2173654288953
      (.node 603086748023662023130
        (.node 2236468005291
          (.node 403
            (.node 601716444270665208199
              (.node 385
                (.node 382
                  (.node 604023606696512606589
                    (.node 584135627113662386556
                      .empty
                      .empty)
                    .empty)
                  (.node 384
                    (.node 2248015579519
                      .empty
                      .empty)
                    .empty))
                (.node 2246672877956
                  (.node 584638922029705286019
                    (.node 2171510737282
                      .empty
                      .empty)
                    .empty)
                  (.node 2250163161478
                    (.node 2245867833733
                      .empty
                      .empty)
                    .empty)))
              (.node 2179563784589
                (.node 2248283654538
                  (.node 2248283916681
                    (.node 2249894824328
                      .empty
                      .empty)
                    .empty)
                  (.node 396
                    (.node 603519119978320449931
                      .empty
                      .empty)
                    .empty))
                (.node 2246404606352
                  (.node 399
                    (.node 2170974112142
                      .empty
                      .empty)
                    .empty)
                  (.node 402
                    (.node 2179291908497
                      .empty
                      .empty)
                    .empty))))
            (.node 2249894431135
              (.node 2177681033625
                (.node 406
                  (.node 405
                    (.node 585576862622807249300
                      .empty
                      .empty)
                    .empty)
                  (.node 2249621342616
                    (.node 2242646313367
                      .empty
                      .empty)
                    .empty))
                (.node 2245867866524
                  (.node 2181170497947
                    (.node 410
                      .empty
                      .empty)
                    .empty)
                  (.node 603879491446428537246
                    (.node 601429317734927208861
                      .empty
                      .empty)
                    .empty)))
              (.node 2243988851109
                (.node 2181170760098
                  (.node 603951496325379608993
                    (.node 585432685867448734112
                      .empty
                      .empty)
                    .empty)
                  (.node 2177148373412
                    (.node 2173922740643
                      .empty
                      .empty)
                    .empty))
                (.node 424
                  (.node 423
                    (.node 2235125778854
                      .empty
                      .empty)
                    .empty)
                  (.node 2241035930026
                    (.node 2246404753833
                      .empty
                      .empty)
                    .empty)))))
          (.node 585072353913572823491
            (.node 439
              (.node 2176879675825
                (.node 2244525771182
                  (.node 429
                    (.node 2175000447404
                      .empty
                      .empty)
                    .empty)
                  (.node 2178221738416
                    (.node 162121702532994206091821750703
                      .empty
                      .empty)
                    .empty))
                (.node 585144490606140625332
                  (.node 161967241007591088583335778739
                    (.node 2249357347250
                      .empty
                      .empty)
                    .empty)
                  (.node 156918464554146095753754483126
                    (.node 157015195130271867167287204277
                      .empty
                      .empty)
                    .empty)))
              (.node 601716475059670979005
                (.node 2180096821690
                  (.node 2181439424953
                    (.node 604094476748203364792
                      .empty
                      .empty)
                    .empty)
                  (.node 2248552253884
                    (.node 2244525525435
                      .empty
                      .empty)
                    .empty))
                (.node 2174191061440
                  (.node 2248552548799
                    (.node 2176342755774
                      .empty
                      .empty)
                    .empty)
                  (.node 2174463822274
                    (.node 449
                      .empty
                      .empty)
                    .empty))))
            (.node 2242910538191
              (.node 2180637755849
                (.node 603951509456709865926
                  (.node 583991507591163318725
                    (.node 585071179565092704708
                      .empty
                      .empty)
                    .empty)
                  (.node 601284133822891332040
                    (.node 585360680973733269959
                      .empty
                      .empty)
                    .empty))
                (.node 603590117638317052364
                  (.node 603519102318488572363
                    (.node 2248552204746
                      .empty
                      .empty)
                    .empty)
                  (.node 2242914732494
                    (.node 2247478675917
                      .empty
                      .empty)
                    .empty)))
              (.node 2180100671957
                (.node 2247209978322
                  (.node 465
                    (.node 2243178842576
                      .empty
                      .empty)
                    .empty)
                  (.node 2246673123796
                    (.node 583918218542487523795
                      .empty
                      .empty)
                    .empty))
                (.node 585144490601044103640
                  (.node 583991507591163318743
                    (.node 2247210240470
                      .empty
                      .empty)
                    .empty)
                  (.node 473
                    .empty
                    .empty))))))
        (.node 2243988670986
          (.node 603735314679258550770
            (.node 603663283476725207526
              (.node 2177953237472
                (.node 2235666909661
                  (.node 584350621212872905180
                    (.node 602437125696242356699
                      .empty
                      .empty)
                    .empty)
                  (.node 583991507595458548191
                    (.node 603951509448119407070
                      .empty
                      .empty)
                    .empty))
                (.node 2180902341091
                  (.node 2166410463714
                    (.node 2174728309217
                      .empty
                      .empty)
                    .empty)
                  (.node 585287457967695942117
                    (.node 2245330930148
                      .empty
                      .empty)
                    .empty)))
              (.node 2178217544172
                (.node 2248015235561
                  (.node 2180097083880
                    (.node 2176611469799
                      .empty
                      .empty)
                    .empty)
                  (.node 2174459415019
                    (.node 2250158361066
                      .empty
                      .empty)
                    .empty))
                (.node 2248279476719
                  (.node 156860441999676263030623427054
                    (.node 157073222406965145092573223405
                      .empty
                      .empty)
                    .empty)
                  (.node 161967243351265508947239590385
                    (.node 496
                      .empty
                      .empty)
                    .empty))))
            (.node 2237541796350
              (.node 2246673320440
                (.node 2240498993653
                  (.node 161754171374667757825437047284
                    (.node 603013564463145144819
                      .empty
                      .empty)
                    .empty)
                  (.node 2235935295991
                    (.node 2248015006198
                      .empty
                      .empty)
                    .empty))
                (.node 2168822319611
                  (.node 35727470840024570
                    (.node 505
                      .empty
                      .empty)
                    .empty)
                  (.node 2171775273469
                    (.node 2180902636028
                      .empty
                      .empty)
                    .empty)))
              (.node 516
                (.node 2174732225025
                  (.node 2177953335808
                    (.node 2246673140223
                      .empty
                      .empty)
                    .empty)
                  (.node 2179828664835
                    (.node 2246673402370
                      .empty
                      .empty)
                    .empty))
                (.node 2248547633671
                  (.node 2175264737798
                    (.node 585360645862912758277
                      .empty
                      .empty)
                    .empty)
                  (.node 521
                    (.node 603590078062072467976
                      .empty
                      .empty)
                    .empty)))))
          (.node 604022476406616920610
            (.node 2170974161430
              (.node 2246673402384
                (.node 2249089452557
                  (.node 2247210043916
                    (.node 602294030852813804043
                      .empty
                      .empty)
                    .empty)
                  (.node 2177148029455
                    (.node 526
                      .empty
                      .empty)
                    .empty))
                (.node 2241836993043
                  (.node 2250158721554
                    (.node 2172848933393
                      .empty
                      .empty)
                    .empty)
                  (.node 2175533369877
                    (.node 2181170366996
                      .empty
                      .empty)
                    .empty)))
              (.node 2177144162844
                (.node 603086778811866436121
                  (.node 2168289593880
                    (.node 2245867833879
                      .empty
                      .empty)
                    .empty)
                  (.node 603229768096545821211
                    (.node 538
                      .empty
                      .empty)
                    .empty))
                (.node 2173926869535
                  (.node 2249357249054
                    (.node 541
                      .empty
                      .empty)
                    .empty)
                  (.node 545
                    (.node 2249089452576
                      .empty
                      .empty)
                    .empty))))
            (.node 603950264803368555054
              (.node 2242373569064
                (.node 585504783038536798757
                  (.node 2173117450788
                    (.node 2172043774499
                      .empty
                      .empty)
                    .empty)
                  (.node 2250162850343
                    (.node 550
                      .empty
                      .empty)
                    .empty))
                (.node 555
                  (.node 2250162850346
                    (.node 2177953597993
                      .empty
                      .empty)
                    .empty)
                  (.node 2180637706797
                    (.node 2174459644460
                      .empty
                      .empty)
                    .empty)))
              (.node 2242109442612
                (.node 2243183053361
                  (.node 2174459382320
                    (.node 585576849360749351471
                      .empty
                      .empty)
                    .empty)
                  (.node 603879469525720797747
                    (.node 562
                      .empty
                      .empty)
                    .empty))
                (.node 2247746603575
                  (.node 566
                    (.node 2167211641397
                      .empty
                      .empty)
                    .empty)
                  (.node 568
                    .empty
                    .empty)))))))
      (.node 584638877981330346648
        (.node 156957164348339121951533587049
          (.node 156492908497102223313001798225
            (.node 2249889778245
              (.node 2242377697855
                (.node 603879363965356282428
                  (.node 571
                    (.node 603085564947539710522
                      .empty
                      .empty)
                    .empty)
                  (.node 2242377959998
                    (.node 2179564571197
                      .empty
                      .empty)
                    .empty))
                (.node 2250162588226
                  (.node 2241572784705
                    (.node 2250162457152
                      .empty
                      .empty)
                    .empty)
                  (.node 2174195403332
                    (.node 2176338938435
                      .empty
                      .empty)
                    .empty)))
              (.node 601572381858879017547
                (.node 584
                  (.node 2172584692295
                    (.node 2177412811334
                      .empty
                      .empty)
                    .empty)
                  (.node 604023567050210431562
                    (.node 2167211641417
                      .empty
                      .empty)
                    .empty))
                (.node 2241035766350
                  (.node 589
                    (.node 2239962090060
                      .empty
                      .empty)
                    .empty)
                  (.node 156879788372652558844191660624
                    (.node 162063978687155557776671201871
                      .empty
                      .empty)
                    .empty))))
            (.node 42174408889685523666019832162754503261
              (.node 2178218216023
                (.node 2244252715604
                  (.node 2248552401491
                    (.node 2574121578303723071570229051350610
                      .empty
                      .empty)
                    .empty)
                  (.node 2178218216022
                    (.node 2237277620821
                      .empty
                      .empty)
                    .empty))
                (.node 2172047706714
                  (.node 2247478348377
                    (.node 2168553949784
                      .empty
                      .empty)
                    .empty)
                  (.node 11321106681833187241906171707044536942684285532
                    (.node 2235130006107
                      .empty
                      .empty)
                    .empty)))
              (.node 2245331110499
                (.node 2246941428320
                  (.node 162063978666113579231169698399
                    (.node 2166406335070
                      .empty
                      .empty)
                    .empty)
                  (.node 156957164328738260035842497122
                    (.node 2170437208673
                      .empty
                      .empty)
                    .empty))
                (.node 2174459890278
                  (.node 2237277620837
                    (.node 2178218216036
                      .empty
                      .empty)
                    .empty)
                  (.node 162063978667266571035797052008
                    (.node 2243715877479
                      .empty
                      .empty)
                    .empty)))))
          (.node 2176606833281
            (.node 2249621441141
              (.node 161831850761248983670879312495
                (.node 2246941887084
                  (.node 2175269128811
                    (.node 2246673271402
                      .empty
                      .empty)
                    .empty)
                  (.node 2243179252334
                    (.node 2168553949805
                      .empty
                      .empty)
                    .empty))
                (.node 162141354661689252027107531378
                  (.node 157111916280039209781449546353
                    (.node 2573804665653657943839730026765936
                      .empty
                      .empty)
                    .empty)
                  (.node 43529593615763858920765767668698653300
                    (.node 2181707319923
                      .empty
                      .empty)
                    .empty)))
              (.node 2243451996795
                (.node 632
                  (.node 2240498993783
                    (.node 585647776722604593782
                      .empty
                      .empty)
                    .empty)
                  (.node 2248820198010
                    (.node 2236472199801
                      .empty
                      .empty)
                    .empty))
                (.node 603373852431992607358
                  (.node 585648858643115938429
                    (.node 157015195129190937352596675196
                      .empty
                      .empty)
                    .empty)
                  (.node 640
                    (.node 161908923324024247577418570367
                      .empty
                      .empty)
                    .empty))))
            (.node 2247210240653
              (.node 2248820492935
                (.node 2243447736964
                  (.node 162121702532994206091821750915
                    (.node 156763722049235423221539707522
                      .empty
                      .empty)
                    .empty)
                  (.node 2246400035462
                    (.node 2176879676037
                      .empty
                      .empty)
                    .empty))
                (.node 2173926754954
                  (.node 603447044790481425033
                    (.node 2179291826824
                      .empty
                      .empty)
                    .empty)
                  (.node 2181439572620
                    (.node 2241299974795
                      .empty
                      .empty)
                    .empty)))
              (.node 602437125700537586323
                (.node 2179828533904
                  (.node 585143303127676572303
                    (.node 2174191192718
                      .empty
                      .empty)
                    .empty)
                  (.node 585503639543218295442
                    (.node 585072397827193279121
                      .empty
                      .empty)
                    .empty))
                (.node 662
                  (.node 602437125696242356885
                    (.node 2249353038484
                      .empty
                      .empty)
                    .empty)
                  (.node 585144455420966982295
                    .empty
                    .empty))))))
        (.node 2244789799624
          (.node 2178754742960
            (.node 582838515717812294308
              (.node 2180902341278
                (.node 585288592603033670299
                  (.node 2180902079130
                    (.node 583991507591163318937
                      .empty
                      .empty)
                    .empty)
                  (.node 2181438737053
                    (.node 2173927066268
                      .empty
                      .empty)
                    .empty))
                (.node 2176606866081
                  (.node 2247478413984
                    (.node 2167748545183
                      .empty
                      .empty)
                    .empty)
                  (.node 675
                    (.node 2245062232738
                      .empty
                      .empty)
                    .empty)))
              (.node 603519097987278181034
                (.node 2166943238823
                  (.node 583702102868410634918
                    (.node 2246668520101
                      .empty
                      .empty)
                    .empty)
                  (.node 583991476740946121385
                    (.node 585144499395790672552
                      .empty
                      .empty)
                    .empty))
                (.node 603806299216251261613
                  (.node 585503639551808754348
                    (.node 602437125696242356907
                      .empty
                      .empty)
                    .empty)
                  (.node 2169896094383
                    (.node 2174459366062
                      .empty
                      .empty)
                    .empty))))
            (.node 603734232834979304124
              (.node 2179291564726
                (.node 2172580580019
                  (.node 2176338823858
                    (.node 689
                      .empty
                      .empty)
                    .empty)
                  (.node 2243720268469
                    (.node 603663248294496326324
                      .empty
                      .empty)
                    .empty))
                (.node 697
                  (.node 584567946358066107064
                    (.node 2237545859767
                      .empty
                      .empty)
                    .empty)
                  (.node 156763720849548526955704457915
                    (.node 161967256356364196103506352826
                      .empty
                      .empty)
                    .empty)))
              (.node 706
                (.node 2174459415231
                  (.node 2244789471934
                    (.node 162063960976479798366044281533
                      .empty
                      .empty)
                    .empty)
                  (.node 157073222406965145092573223617
                    (.node 2243451931328
                      .empty
                      .empty)
                    .empty))
                (.node 2167215819461
                  (.node 2175805868740
                    (.node 2239425120963
                      .empty
                      .empty)
                    .empty)
                  (.node 2239689214663
                    (.node 2244525771462
                      .empty
                      .empty)
                    .empty)))))
          (.node 2170437225184
            (.node 2236740684500
              (.node 601789636491446637262
                (.node 2249626372811
                  (.node 2175537334986
                    (.node 2239962106569
                      .empty
                      .empty)
                    .empty)
                  (.node 2246404901581
                    (.node 2243183528652
                      .empty
                      .empty)
                    .empty))
                (.node 2243183528657
                  (.node 2246400363216
                    (.node 2180902701775
                      .empty
                      .empty)
                    .empty)
                  (.node 2239693408979
                    (.node 585072340648562102994
                      .empty
                      .empty)
                    .empty)))
              (.node 2249085029082
                (.node 162063976324385949761650432727
                  (.node 157053867787573712039182424790
                    (.node 2168017013461
                      .empty
                      .empty)
                    .empty)
                  (.node 2248015661785
                    (.node 2179291990744
                      .empty
                      .empty)
                    .empty))
                (.node 2244793846493
                  (.node 2172849146588
                    (.node 585432690194355720923
                      .empty
                      .empty)
                    .empty)
                  (.node 603662175171684864735
                    (.node 2166406302430
                      .empty
                      .empty)
                    .empty))))
            (.node 585575723525266756332
              (.node 2180365552358
                (.node 2249088944867
                  (.node 2235129973474
                    (.node 2172849146593
                      .empty
                      .empty)
                    .empty)
                  (.node 2243984444133
                    (.node 2176070568676
                      .empty
                      .empty)
                    .empty))
                (.node 745
                  (.node 2174463707880
                    (.node 743
                      .empty
                      .empty)
                    .empty)
                  (.node 747
                    (.node 585072415421531509482
                      .empty
                      .empty)
                    .empty)))
              (.node 603158845204149572338
                (.node 584856194326668284655
                  (.node 750
                    (.node 604023593442516079341
                      .empty
                      .empty)
                    .empty)
                  (.node 583702107264309547761
                    (.node 752
                      .empty
                      .empty)
                    .empty))
                (.node 757
                  (.node 2247746865908
                    (.node 585072415419379520243
                      .empty
                      .empty)
                    .empty)
                  (.node 758
                    .empty
                    .empty)))))))))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
